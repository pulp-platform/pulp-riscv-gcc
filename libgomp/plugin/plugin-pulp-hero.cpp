/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Author: Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 * 
 * Copyright (C) 2005-2014 Free Software Foundation, Inc.
 * 
 * This file is part of the GNU OpenMP Library (libgomp).
 * 
 * Libgomp is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 * 
 * Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 * 
 * Under Section 7 of GPL version 3, you are granted additional
 * permissions described in the GCC Runtime Library Exception, version
 * 3.1, as published by the Free Software Foundation.
 * 
 * You should have received a copy of the GNU General Public License and
 * a copy of the GCC Runtime Library Exception along with this program;
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

/* Simple implementation of support routines for a shared-memory
   acc_device_host, and a non-shared memory acc_device_host_nonshm, with the
   latter built as a plugin.  */

#include "config.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <inttypes.h>
#include <stdbool.h>
#include <vector>
#include <map>

#include "libgomp-plugin.h"
#include "gomp-constants.h"

#define DEBUG
#ifdef DEBUG
#define TRACE(...) do { \
  printf("[%s:%d:%s]: ", __FILE__, __LINE__, __func__); \
  printf(__VA_ARGS__); \
  printf("\n"); \
} while (0)
#else
#define TRACE(...) do { \
} while (0)
#endif

extern "C"
{
  #include "pulp.h"
  #define PULP_HERO_DEFAULT_CLUSTER_ID    (0x1U)
  #define PULP_HERO_DEFAULT_FREQ          (PULP_DEFAULT_FREQ_MHZ)
  #define PULP_HERO_DEFAULT_MEM_MODE      (copy)
  #define PULP_HERO_DEFAULT_RAB_LEVEL     (0x0U)
  #define PULP_HERO_DEFAULT_RAB_LOG_EN    (0x0U)
  #define PULP_HERO_DEFAULT_ACP_EN        (0x0U)
  #define PULP_HERO_DEFAULT_TIMEOUT       ( 20U)
}

/* Start/end addresses of functions and global variables on a device.  */
typedef std::vector<addr_pair> AddrVect;

/* Addresses of functions variables map on a device.  */
typedef std::map<uintptr_t, DataDesc> AddrVectMap;

/* Addresses for all images and a device.  */
typedef std::map<const void *, AddrVect> ImgDevAddrMap;

/* Total number of available devices.  */
static int num_devices;

/* Total number of shared libraries with offloading to PULP.  */
static int num_images;

/* Two dimensional array: one key is a pointer to image,
   second key is number of device.  Contains a vector of pointer pairs.  */
static ImgDevAddrMap *address_table;
static AddrVectMap *address_map;

/* Thread-safe registration  */
static pthread_once_t is_init_hero_device = PTHREAD_ONCE_INIT;

/* PULP device handlers.  */
static PulpDev pulp_dev;
static PulpDev *pulp;

#define GOMP(X) GOMP_PLUGIN_##X
#define SELF "pulp: "

extern "C" const char *
GOMP_OFFLOAD_get_name (void)
{
  return "pulp-hero";
}

extern "C" unsigned int
GOMP_OFFLOAD_get_caps (void)
{
  TRACE("");
  return GOMP_OFFLOAD_CAP_SHARED_MEM | GOMP_OFFLOAD_CAP_OPENMP_400;
}

extern "C" int
GOMP_OFFLOAD_get_type (void)
{
  TRACE("");
  return OFFLOAD_TARGET_TYPE_PULP_HERO;
}

extern "C" int
GOMP_OFFLOAD_get_num_devices (void)
{
  TRACE("");
  return 1;

}

static void
init_hero_device()
{
  int currFreq = 0x0;
  int ret      = 0x1;

  pulp = &pulp_dev;
  pulp->cluster_sel   = PULP_HERO_DEFAULT_CLUSTER_ID;
  pulp->rab_ax_log_en = PULP_HERO_DEFAULT_RAB_LOG_EN;

  // reserve virtual addresses overlapping with PULP's internal physical address space
  pulp_reserve_v_addr(pulp);
  pulp_mmap(pulp);
  pulp_reset(pulp, 0x1);

  currFreq = pulp_clking_set_freq(pulp, PULP_HERO_DEFAULT_FREQ);
  if (currFreq > 0)
    TRACE("PULP HERO device on @ %d MHz.", currFreq);
  else
    GOMP_PLUGIN_fatal ("PULP HERO device init failed!");

  pulp_rab_free(pulp,0x0);

  // initialization of PULP, static RAB rules (mbox, L2, ...)
  pulp_init(pulp);

  address_table = new ImgDevAddrMap;
  address_map = new AddrVectMap;
  num_devices = 1;
  num_images = 0;
}

extern "C" bool
GOMP_OFFLOAD_init_device (int n __attribute__ ((unused)))
{
  TRACE("");
  pthread_once (&is_init_hero_device, init_hero_device);
  return 1;
}

extern "C" bool
GOMP_OFFLOAD_fini_device (int n __attribute__ ((unused)))
{
  TRACE("");
  pulp_mbox_write(pulp, PULP_START);
  pulp_mbox_write(pulp, 0xdeadbeef);
  pulp_mbox_write(pulp, NULL);

  TRACE("waiting EOC");
  pulp_exe_wait(pulp,PULP_HERO_DEFAULT_TIMEOUT); 
  return 0x1;
}

/* Return the libgomp version number we're compatible with.  There is
   no requirement for cross-version compatibility.  */

extern "C" unsigned
GOMP_OFFLOAD_version (void)
{
  return GOMP_VERSION;
}


static void
get_target_table (int &num_funcs, int &num_vars, void **&table)
{
  /* Boot Pulp Device*/
  pulp_exe_start(pulp);

  pulp_mbox_read(pulp, (unsigned int * ) &num_funcs, 1);
  pulp_mbox_read(pulp, (unsigned int * ) &num_vars, 1);

  int table_size = num_funcs + 2 * num_vars;
  table = new void * [table_size];

  if(num_funcs) {
    for(int i = 0; i < num_funcs; i++) {
      pulp_mbox_read(pulp, (unsigned int * ) &table[i], 1);
      TRACE ("func%d: %x, ", i, table[i]);
    }
  }
  
  if(num_vars) {
    for(int i = 0; i < num_vars; i++) {
      pulp_mbox_read(pulp, (unsigned int * ) &table[i*2+num_vars], 1);
      pulp_mbox_read(pulp, (unsigned int * ) &table[i*2+1+num_vars], 1);
      TRACE ("var%d: %x size %x, ", i, table[i*2+num_vars], table[i*2+1+num_vars]);
    }
  }
}

/* Offload TARGET_IMAGE to all available devices and fill address_table with
   corresponding target addresses.  */
static void
offload_image (const void *target_image)
{
  struct TargetImage {
    int64_t size;
    /* 10 characters is enough for max int value.  */
    char name[sizeof ("lib0000000000.so")];
    char data[];
  } __attribute__ ((packed));

  void *image_start = ((void **) target_image)[0];
  void *image_end   = ((void **) target_image)[1];
  int64_t image_size = (uintptr_t) image_end - (uintptr_t) image_start;
  
  TRACE ("(target_images = %p { %p, %p, %d })",
   target_image, image_start, image_end, image_size);

  TargetImage *image
    = (TargetImage *) malloc (sizeof (int64_t) + sizeof ("lib0000000000.so")
            + image_size);
  if (!image)
    {
      fprintf (stderr, "%s: Can't allocate memory\n", __FILE__);
      exit (1);
    }

  image->size = image_size;
  sprintf (image->name, "lib%010d.so", num_images++);
  pulp_load_bin_from_mem(pulp, image_start, image->size);
  TRACE ("Pulp Loaded image %s { %x, %d }", image->name, image_start, image->size );

  int num_funcs = 0;
  int num_vars = 0;
  void **table = NULL;

  get_target_table (num_funcs, num_vars, table);

  AddrVect curr_dev_table;
  for (int i = 0; i < num_funcs; i++)
  {
    addr_pair tgt_addr;
    tgt_addr.start = (uintptr_t) table[i];
    tgt_addr.end = tgt_addr.start + 1;
    TRACE ("() func %d:\t0x%llx..0x%llx", i,
     tgt_addr.start, tgt_addr.end);
    curr_dev_table.push_back (tgt_addr);
  }

  for (int i = 0; i < num_vars; i++)
  {
    addr_pair tgt_addr;
    tgt_addr.start = (uintptr_t) table[num_funcs+i*2];
    tgt_addr.end = tgt_addr.start + (uintptr_t) table[num_funcs+i*2+1];
    TRACE ("() var %d:\t0x%llx..0x%llx", i, tgt_addr.start, tgt_addr.end);
    curr_dev_table.push_back (tgt_addr);
  }
  address_table->insert (std::make_pair (target_image, curr_dev_table));
  free (image);
}

extern "C" int
GOMP_OFFLOAD_load_image (int device __attribute__ ((unused)),
       unsigned int version __attribute__ ((unused)),
       const void *target_image __attribute__ ((unused)),
       struct addr_pair **result __attribute__ ((unused)))
{
  TRACE ("(device = %d, version = %d, target_image = %p, result = %p)", device, version, target_image, result);

  if (GOMP_VERSION_DEV (version) > GOMP_VERSION)
  {
    GOMP_PLUGIN_error ("Offload data incompatible with HERO plugin"
      " (expected %u, received %u)",
      GOMP_VERSION, GOMP_VERSION_DEV (version));
    return -1;
  }

  /* If target_image is already present in address_table, then there is no need
     to offload it.  */
  if (address_table->count (target_image) == 0)
    offload_image (target_image);

  AddrVect *curr_dev_table = &(*address_table)[target_image];
  int table_size = curr_dev_table->size ();
  addr_pair *table = (addr_pair *) malloc (table_size * sizeof (addr_pair));
  if (table == NULL)
    {
      fprintf (stderr, "%s: Can't allocate memory\n", __FILE__);
      exit (1);
    }

  std::copy (curr_dev_table->begin (), curr_dev_table->end (), table);
  *result = table;
  return table_size;
}

extern "C" bool
GOMP_OFFLOAD_unload_image (int n __attribute__ ((unused)),
                           unsigned int version __attribute__ ((unused)),
                           const void *i __attribute__ ((unused)))
{
  TRACE("");
  return 0x1;  
}

void *base_address;

extern "C" void *
GOMP_OFFLOAD_alloc (int n __attribute__ ((unused)), size_t size)
{
  TRACE("");

  uintptr_t phy_ptr = NULL;
  uintptr_t virt_ptr = NULL;
  DataDesc data_desc;
  
  virt_ptr = (uintptr_t) pulp_l3_malloc(pulp, size, &phy_ptr);

  data_desc.sh_mem_ctrl = PULP_HERO_DEFAULT_MEM_MODE;
  data_desc.cache_ctrl = PULP_HERO_DEFAULT_ACP_EN;
  data_desc.rab_lvl = PULP_HERO_DEFAULT_RAB_LEVEL;
  data_desc.ptr_l3_v = (void *) virt_ptr; //FIXME this should not be required
  data_desc.ptr_l3_p = (void *) phy_ptr;
  data_desc.size = size;

  TRACE("data_desc.sh_mem_ctrl = %x", data_desc.sh_mem_ctrl);
  TRACE("data_desc.cache_ctrl = %x", data_desc.cache_ctrl);
  TRACE("data_desc.rab_lvl = %x", data_desc.rab_lvl);
  TRACE("data_desc.ptr_l3_v = %x", data_desc.ptr_l3_v);
  TRACE("data_desc.ptr_l3_p = %x", data_desc.ptr_l3_p);
  TRACE("data_desc.size = %x", data_desc.size);
  TRACE("address_map->insert: %x", data_desc.ptr_l3_p);

  address_map->insert (std::make_pair (phy_ptr, data_desc));
  base_address = (void *) phy_ptr;
  return (void *) phy_ptr;
}

extern "C" bool
GOMP_OFFLOAD_free (int n __attribute__ ((unused)), void *tgt_ptr)
{
  TRACE("tgt_ptr = %x", tgt_ptr);
  uintptr_t vir_ptr = (uintptr_t) (address_map->find((uintptr_t)tgt_ptr)->second).ptr_l3_v;
  uintptr_t phy_ptr = (uintptr_t) tgt_ptr;
  address_map->erase (phy_ptr);

  pulp_l3_free(pulp, vir_ptr, phy_ptr);
}

extern "C" bool
GOMP_OFFLOAD_host2dev (int n __attribute__ ((unused)),
                       void *tgt_ptr, const void *host_ptr,
                       size_t size)
{
  DataDesc &data_desc = address_map->find((uintptr_t)base_address)->second;
  uintptr_t offset = (uintptr_t) tgt_ptr - (uintptr_t) base_address;
  uintptr_t vir_ptr = (uintptr_t) data_desc.ptr_l3_v + offset;

  TRACE ("(tgt_ptr = %p, host_ptr = %p, size = %d)", tgt_ptr, host_ptr, size);
  TRACE ("memcpy(vir_ptr = %p, host_ptr = %p, size = %d)", vir_ptr, host_ptr, size);
  memcpy((void *) vir_ptr, host_ptr, size);
  return 0x1;
}

extern "C" bool
GOMP_OFFLOAD_dev2host (int n __attribute__ ((unused)),
                       void *host_ptr, const void *tgt_ptr,
                       size_t size)
{
  DataDesc &data_desc = address_map->find((uintptr_t)base_address)->second;
  uintptr_t offset = (uintptr_t) tgt_ptr - (uintptr_t) base_address;
  uintptr_t vir_ptr = (uintptr_t) data_desc.ptr_l3_v + offset;

  TRACE ("(host_ptr = %p, tgt_ptr = %p, size = %d)", host_ptr, tgt_ptr, size);
  TRACE ("memcpy(host_ptr = %p, vir_ptr = %p, size = %d)", host_ptr, vir_ptr, size);
  memcpy(host_ptr, (void *) vir_ptr, size);
  return 0x1;  
}

extern "C" bool
GOMP_OFFLOAD_dev2dev (int n __attribute__ ((unused)),
                       void *host_ptr, const void *tgt_ptr,
                       size_t size)
{
  TRACE("");
  GOMP_PLUGIN_fatal("Not supported!");
  return 0;
}

extern "C" void
GOMP_OFFLOAD_run (int n __attribute__ ((unused)), void *tgt_fn, void *tgt_vars, void **args __attribute__ ((unused)))
{
  uint32_t ret;

  TRACE ("*(tgt_fn = %p, tgt_vars = %p (%p))", tgt_fn,
         tgt_vars);
  pulp_mbox_write(pulp, PULP_START);
  pulp_mbox_write(pulp, (uint32_t) tgt_fn);
  pulp_mbox_write(pulp, (uint32_t) tgt_vars);
  usleep(10);
  pulp_mbox_read(pulp, (unsigned int * ) &ret, 1);
  if(ret == PULP_DONE)
      TRACE ("execution done");
  else
      TRACE ("returned %d", ret);
}

void
GOMP_OFFLOAD_async_run (int ord, void *tgt_fn, void *tgt_vars, void **args,
      void *async_data)
{
  TRACE ("(tgt_fn = %p, tgt_vars = %p (%p))", tgt_fn,
         tgt_vars);
}
