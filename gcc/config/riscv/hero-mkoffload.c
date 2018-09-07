/*
 * Offload image generation tool for RISC-V PULP HERO device.
 *
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Author: Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 * 
 * This file is part of GCC.
 * 
 * GCC is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 * 
 * GCC is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with GCC; see the file COPYING3.  If not see
 * <http://www.gnu.org/licenses/>.
 */

#include "config.h"
#include <libgen.h>
#include "system.h"
#include "coretypes.h"
#include "obstack.h"
#include "intl.h"
#include "diagnostic.h"
#include "collect-utils.h"
#include "hero-offload.h"

const char tool_name[] = "HERO mkoffload";
const char image_section_name[] = ".gnu.offload_images";
const char *symbols[3] = { "__offload_image_pulp_start",
         "__offload_image_pulp_end",
         "__offload_image_pulp_size" };
const char *out_obj_filename = NULL;

int num_temps = 0;
const int MAX_NUM_TEMPS = 10;
const char *temp_files[MAX_NUM_TEMPS];

/* Delete tempfiles and exit function.  */
void
tool_cleanup (bool from_signal ATTRIBUTE_UNUSED)
{
  for (int i = 0; i < num_temps; i++)
    maybe_unlink (temp_files[i]);
}

static void
mkoffload_cleanup (void)
{
  tool_cleanup (false);
}

/* Unlink FILE unless requested otherwise.  */

void
maybe_unlink (const char *file)
{
  if (!save_temps)
    {
      if (unlink_if_ordinary (file)
	  && errno != ENOENT)
	fatal_error (input_location, "deleting file %s: %m", file);
    }
  else if (verbose)
    fprintf (stderr, "[Leaving %s]\n", file);
}

/* Add or change the value of an environment variable, outputting the
   change to standard error if in verbose mode.  */
static void
xputenv (const char *string)
{
  if (verbose)
    fprintf (stderr, "%s\n", string);
  putenv (CONST_CAST (char *, string));
}

/* Parse STR, saving found tokens into PVALUES and return their number.
   Tokens are assumed to be delimited by ':'.  */
static unsigned
parse_env_var (const char *str, char ***pvalues)
{
  const char *curval, *nextval;
  char **values;
  unsigned num = 1, i;

  curval = strchr (str, ':');
  while (curval)
    {
      num++;
      curval = strchr (curval + 1, ':');
    }

  values = (char **) xmalloc (num * sizeof (char *));
  curval = str;
  nextval = strchr (curval, ':');
  if (nextval == NULL)
    nextval = strchr (curval, '\0');

  for (i = 0; i < num; i++)
    {
      int l = nextval - curval;
      values[i] = (char *) xmalloc (l + 1);
      memcpy (values[i], curval, l);
      values[i][l] = 0;
      curval = nextval + 1;
      nextval = strchr (curval, ':');
      if (nextval == NULL)
	nextval = strchr (curval, '\0');
    }
  *pvalues = values;
  return num;
}

/* Auxiliary function that frees elements of PTR and PTR itself.
   N is number of elements to be freed.  If PTR is NULL, nothing is freed.
   If an element is NULL, subsequent elements are not freed.  */
static void
free_array_of_ptrs (void **ptr, unsigned n)
{
  unsigned i;
  if (!ptr)
    return;
  for (i = 0; i < n; i++)
    {
      if (!ptr[i])
	break;
      free (ptr[i]);
    }
  free (ptr);
  return;
}

/* Check whether NAME can be accessed in MODE.  This is like access,
   except that it never considers directories to be executable.  */
static int
access_check (const char *name, int mode)
{
  if (mode == X_OK)
    {
      struct stat st;

      if (stat (name, &st) < 0 || S_ISDIR (st.st_mode))
	return -1;
    }

  return access (name, mode);
}

/* Find target compiler using a path from COLLECT_GCC or COMPILER_PATH.  */
static char *
find_target_compiler (const char *name)
{
  bool found = false;
  char **paths = NULL;
  unsigned n_paths, i;
  char *target_compiler;
  const char *collect_gcc = getenv ("COLLECT_GCC");
  const char *gcc_path = dirname (ASTRDUP (collect_gcc));
  const char *gcc_exec = basename (ASTRDUP (collect_gcc));

  if (strcmp (gcc_exec, collect_gcc) == 0)
    {
      /* collect_gcc has no path, so it was found in PATH.  Make sure we also
	 find accel-gcc in PATH.  */
      target_compiler = XDUPVEC (char, name, strlen (name) + 1);
      found = true;
      goto out;
    }

  target_compiler = concat (gcc_path, "/", name, NULL);
  if (access_check (target_compiler, X_OK) == 0)
    {
      found = true;
      goto out;
    }

  n_paths = parse_env_var (getenv ("COMPILER_PATH"), &paths);
  for (i = 0; i < n_paths; i++)
    {
      size_t len = strlen (paths[i]) + 1 + strlen (name) + 1;
      target_compiler = XRESIZEVEC (char, target_compiler, len);
      sprintf (target_compiler, "%s/%s", paths[i], name);
      if (access_check (target_compiler, X_OK) == 0)
	{
	  found = true;
	  break;
	}
    }

out:
  free_array_of_ptrs ((void **) paths, n_paths);
  return found ? target_compiler : NULL;
}

static void
compile_for_target (struct obstack *argv_obstack)
{
  obstack_ptr_grow (argv_obstack, NULL);
  char **argv = XOBFINISH (argv_obstack, char **);

  /* Save environment variables.  */
  const char *epath = getenv ("GCC_EXEC_PREFIX");
  const char *cpath = getenv ("COMPILER_PATH");
  const char *lpath = getenv ("LIBRARY_PATH");
  const char *rpath = getenv ("LD_RUN_PATH");
  unsetenv ("GCC_EXEC_PREFIX");
  unsetenv ("COMPILER_PATH");
  unsetenv ("LIBRARY_PATH");
  unsetenv ("LD_RUN_PATH");

  /* Diagnostic -- Start */
  // char cmd[1024*4] = "";
  // int i = 0;
  // while(argv[i] != NULL){
  //   strcat(cmd, argv[i]);
  //   strcat(cmd, " ");
  //   i++;
  // }
  // inform(input_location, "%s\n", cmd);
  /* Diagnostic -- End */

  fork_execute (argv[0], argv, false);
  obstack_free (argv_obstack, NULL);

  /* Restore environment variables.  */
  xputenv (concat ("GCC_EXEC_PREFIX=", epath, NULL));
  xputenv (concat ("COMPILER_PATH=", cpath, NULL));
  xputenv (concat ("LIBRARY_PATH=", lpath, NULL));
  xputenv (concat ("LD_RUN_PATH=", rpath, NULL));
}

/* Generates object file with the descriptor for the target library.  */
static const char *
generate_target_descr_file (const char *target_compiler)
{
  const char *src_filename = make_temp_file ("_target_descr.c");
  const char *obj_filename = make_temp_file ("_target_descr.o");
  temp_files[num_temps++] = src_filename;
  temp_files[num_temps++] = obj_filename;
  FILE *src_file = fopen (src_filename, "w");

  if (!src_file)
    fatal_error (input_location, "cannot open '%s'", src_filename);

  fprintf (src_file,
	   "extern const void *const __offload_funcs_end[];\n"
	   "extern const void *const __offload_vars_end[];\n\n"

	   "const void *const __offload_func_table[0]\n"
	   "__attribute__ ((__used__, visibility (\"hidden\"),\n"
	   "section (\".gnu.offload_funcs\"))) = { };\n\n"

	   "const void *const __offload_var_table[0]\n"
	   "__attribute__ ((__used__, visibility (\"hidden\"),\n"
	   "section (\".gnu.offload_vars\"))) = { };\n\n"

	   "const void *const __OFFLOAD_TARGET_TABLE__[]\n"
	   "__attribute__ ((__used__, visibility (\"hidden\"))) = {\n"
	   "  &__offload_func_table, &__offload_funcs_end,\n"
	   "  &__offload_var_table, &__offload_vars_end\n"
	   "};\n\n");

  fprintf (src_file,
	   "#ifdef __cplusplus\n"
	   "extern \"C\"\n"
	   "#endif\n"
	   "void target_register_lib (const void *);\n\n"

	   "__attribute__((constructor))\n"
	   "static void\n"
	   "init (void)\n"
	   "{\n"
	   "  target_register_lib (__OFFLOAD_TARGET_TABLE__);\n"
	   "}\n");
  fclose (src_file);

  struct obstack argv_obstack;
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, target_compiler);
  obstack_ptr_grow (&argv_obstack, "-c");
  obstack_ptr_grow (&argv_obstack, "-shared");
  obstack_ptr_grow (&argv_obstack, "-fPIC");
  obstack_ptr_grow (&argv_obstack, src_filename);
  obstack_ptr_grow (&argv_obstack, "-o");
  obstack_ptr_grow (&argv_obstack, obj_filename);
  compile_for_target (&argv_obstack);

  return obj_filename;
}

/* Generates object file with __offload_*_end symbols for the target
   library.  */
static const char *
generate_target_offloadend_file (const char *target_compiler)
{
  const char *src_filename = make_temp_file ("_target_offloadend.c");
  const char *obj_filename = make_temp_file ("_target_offloadend.o");
  temp_files[num_temps++] = src_filename;
  temp_files[num_temps++] = obj_filename;
  FILE *src_file = fopen (src_filename, "w");

  if (!src_file)
    fatal_error (input_location, "cannot open '%s'", src_filename);

  fprintf (src_file,
	   "const void *const __offload_funcs_end[0]\n"
	   "__attribute__ ((__used__, visibility (\"hidden\"),\n"
	   "section (\".gnu.offload_funcs\"))) = { };\n\n"

	   "const void *const __offload_vars_end[0]\n"
	   "__attribute__ ((__used__, visibility (\"hidden\"),\n"
	   "section (\".gnu.offload_vars\"))) = { };\n");
  fclose (src_file);

  struct obstack argv_obstack;
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, target_compiler);
  obstack_ptr_grow (&argv_obstack, "-c");
  obstack_ptr_grow (&argv_obstack, "-shared");
  obstack_ptr_grow (&argv_obstack, "-fPIC");
  obstack_ptr_grow (&argv_obstack, src_filename);
  obstack_ptr_grow (&argv_obstack, "-o");
  obstack_ptr_grow (&argv_obstack, obj_filename);
  compile_for_target (&argv_obstack);

  return obj_filename;
}

/* Generates object file with the host side descriptor.  */
static const char *
generate_host_descr_file (const char *host_compiler)
{
  const char *src_filename = make_temp_file ("_host_descr.c");
  const char *obj_filename = make_temp_file ("_host_descr.o");
  temp_files[num_temps++] = src_filename;
  temp_files[num_temps++] = obj_filename;
  FILE *src_file = fopen (src_filename, "w");

  if (!src_file)
    fatal_error (input_location, "cannot open '%s'", src_filename);

  fprintf (src_file,
     "extern const void *const __OFFLOAD_TABLE__;\n"
     "extern const void *const __offload_image_pulp_start;\n"
     "extern const void *const __offload_image_pulp_end;\n\n"

     "static const void *const __offload_target_data[] = {\n"
     "  &__offload_image_pulp_start, &__offload_image_pulp_end\n"
     "};\n\n");

  fprintf (src_file,
	   "#ifdef __cplusplus\n"
	   "extern \"C\"\n"
	   "#endif\n"
	   "void GOMP_offload_register (const void *, int, const void *);\n"
	   "#ifdef __cplusplus\n"
	   "extern \"C\"\n"
	   "#endif\n"
	   "void GOMP_offload_unregister (const void *, int, const void *);\n\n"

     "__attribute__((constructor))\n"
     "static void\n"
     "init (void)\n"
     "{\n"
     "  GOMP_offload_register (&__OFFLOAD_TABLE__, %d, __offload_target_data);\n"
     "}\n\n", GOMP_DEVICE_PULP_HERO);

  fprintf (src_file,
     "__attribute__((destructor))\n"
     "static void\n"
     "fini (void)\n"
     "{\n"
     "  GOMP_offload_unregister (&__OFFLOAD_TABLE__, %d, __offload_target_data);\n"
     "}\n", GOMP_DEVICE_PULP_HERO);

  fclose (src_file);

  unsigned new_argc = 0;
  const char *new_argv[9];
  new_argv[new_argc++] = host_compiler;
  new_argv[new_argc++] = "-c";
  new_argv[new_argc++] = "-fPIC";
  new_argv[new_argc++] = "-shared";
  new_argv[new_argc++] = src_filename;
  new_argv[new_argc++] = "-o";
  new_argv[new_argc++] = obj_filename;
  new_argv[new_argc++] = NULL;
  fork_execute (new_argv[0], CONST_CAST (char **, new_argv), false);

  return obj_filename;
}

static const char *
prepare_target_image (const char *target_compiler, int argc, char **argv)
{
  const char *target_descr_filename
    = generate_target_descr_file (target_compiler);
  const char *target_offloadend_filename
    = generate_target_offloadend_file (target_compiler);

  char *opt1
    = XALLOCAVEC (char, sizeof ("-Wl,") + strlen (target_descr_filename));
  char *opt2
    = XALLOCAVEC (char, sizeof ("-Wl,") + strlen (target_offloadend_filename));
  sprintf (opt1, "-Wl,%s", target_descr_filename);
  sprintf (opt2, "-Wl,%s", target_offloadend_filename);

  const char *target_o_filename = make_temp_file ("_offload.o");
  temp_files[num_temps++] = target_o_filename;
  const char *target_so_filename = make_temp_file ("_offload_pulp.so");
  temp_files[num_temps++] = target_so_filename;

  /* Add HERO compilation flags  */
  const char *PULP_HERO_EXTCFLAGS = getenv("PULP_HERO_EXTCFLAGS");
  char **hero_cflags = buildargv(PULP_HERO_EXTCFLAGS);
  const char *PULP_HERO_EXTLDFLAGS = getenv("PULP_HERO_EXTLDFLAGS");
  char **hero_ldflags = buildargv(PULP_HERO_EXTLDFLAGS);

  /* Here we compile the target GIMPLE using xlto frontend */
  /* The output will be the "target_o_filename"            */
  struct obstack argv_obstack;
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, target_compiler);
  obstack_ptr_grow (&argv_obstack, "-c");
  obstack_ptr_grow (&argv_obstack, "-xlto");
  for(int i = 0; i < countargv(hero_cflags); i++)
    obstack_ptr_grow (&argv_obstack, hero_cflags[i]);

  for (int i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-o") && i + 1 != argc)
      out_obj_filename = argv[++i];
    else if (strcmp (argv[i], "-fopenmp"))
      obstack_ptr_grow (&argv_obstack, argv[i]);
  }
  obstack_ptr_grow (&argv_obstack, "-o");
  obstack_ptr_grow (&argv_obstack, target_o_filename);
  compile_for_target (&argv_obstack);
  
  /* Diagnostic -- Start */
  //obstack_init (&argv_obstack);
  //obstack_ptr_grow (&argv_obstack, "cp");
  //obstack_ptr_grow (&argv_obstack, target_o_filename);
  //obstack_ptr_grow (&argv_obstack, "target.so");
  //obstack_ptr_grow (&argv_obstack, NULL);
  //char **objargs2 = XOBFINISH (&argv_obstack, char **);
  //fork_execute (objargs2[0], objargs2, false);
  /* Diagnostic -- End */

  /* Now we link all togheter with the PULP                *
   * runtime libraries. We genereates "target_so_filename" */
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, target_compiler);
  for(int i = 0; i < countargv(hero_cflags); i++)
    obstack_ptr_grow (&argv_obstack, hero_cflags[i]);
  obstack_ptr_grow (&argv_obstack, "-flto");
  obstack_ptr_grow (&argv_obstack, opt1);
  /* Here we remove from args the *.o input files */
  /* beacuse we have already compiled them previously */
  for (int i = 1; i < argc; i++)
  {
    if (!strcmp (argv[i], "-o") && i + 1 != argc)
      out_obj_filename = argv[++i];
    else if (strcmp (argv[i], "-fopenmp"))
      if (!(strrchr(argv[i], '.') && !strcmp(strrchr(argv[i], '.'), ".o")))
        // Skip *.o files
        obstack_ptr_grow (&argv_obstack, argv[i]);
  }
  obstack_ptr_grow (&argv_obstack, target_o_filename);
  obstack_ptr_grow (&argv_obstack, opt2);
  for(int i = 0; i < countargv(hero_ldflags); i++)
    obstack_ptr_grow (&argv_obstack, hero_ldflags[i]);
  obstack_ptr_grow (&argv_obstack, "-o");
  obstack_ptr_grow (&argv_obstack, target_so_filename);
  compile_for_target (&argv_obstack);

  /* Diagnostic -- Start */
  // obstack_init (&argv_obstack);
  // obstack_ptr_grow (&argv_obstack, "cp");
  // obstack_ptr_grow (&argv_obstack, target_so_filename);
  // obstack_ptr_grow (&argv_obstack, "offload.so");
  // obstack_ptr_grow (&argv_obstack, NULL);
  // char **objargs2 = XOBFINISH (&argv_obstack, char **);
  // fork_execute (objargs2[0], objargs2, false);
  /* Diagnostic -- End */


  freeargv(hero_cflags);
  freeargv(hero_ldflags);

  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, "riscv32-unknown-elf-objcopy");
  obstack_ptr_grow (&argv_obstack, "--only-section=.vectors");
  obstack_ptr_grow (&argv_obstack, "--only-section=.preinit_array");
  obstack_ptr_grow (&argv_obstack, "--only-section=.init_array");
  obstack_ptr_grow (&argv_obstack, "--only-section=.fini_array");
  obstack_ptr_grow (&argv_obstack, "--only-section=.boot");
  obstack_ptr_grow (&argv_obstack, "--only-section=.text");
  obstack_ptr_grow (&argv_obstack, "--only-section=.rodata");
  obstack_ptr_grow (&argv_obstack, "--only-section=.data");
  obstack_ptr_grow (&argv_obstack, "--only-section=.heapl2ram");
  obstack_ptr_grow (&argv_obstack, "--only-section=.bss");
  obstack_ptr_grow (&argv_obstack, "--only-section=.shared");
  obstack_ptr_grow (&argv_obstack, "-O");
  obstack_ptr_grow (&argv_obstack, "binary");
  obstack_ptr_grow (&argv_obstack, target_so_filename);
  compile_for_target (&argv_obstack);

  /* Diagnostic -- Start */
  // obstack_init (&argv_obstack);
  // obstack_ptr_grow (&argv_obstack, "cp");
  // obstack_ptr_grow (&argv_obstack, target_so_filename);
  // obstack_ptr_grow (&argv_obstack, "offload.bin");
  // obstack_ptr_grow (&argv_obstack, NULL);
  // objargs2 = XOBFINISH (&argv_obstack, char **);
  // fork_execute (objargs2[0], objargs2, false);
  /* Diagnostic -- End */

  /* Run objcopy.  */
  char *rename_section_opt
     = XALLOCAVEC (char, sizeof (".data=") + strlen (image_section_name));
  sprintf (rename_section_opt, ".data=%s", image_section_name);

  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, "arm-linux-gnueabihf-objcopy");
  obstack_ptr_grow (&argv_obstack, "-B");
  obstack_ptr_grow (&argv_obstack, "arm");
  obstack_ptr_grow (&argv_obstack, "-I");
  obstack_ptr_grow (&argv_obstack, "binary");
  obstack_ptr_grow (&argv_obstack, "-O");
  obstack_ptr_grow (&argv_obstack, "elf32-littlearm");
  obstack_ptr_grow (&argv_obstack, target_so_filename);
  obstack_ptr_grow (&argv_obstack, "--rename-section");
  obstack_ptr_grow (&argv_obstack, rename_section_opt);
  obstack_ptr_grow (&argv_obstack, NULL);

  char **objargs = XOBFINISH (&argv_obstack, char **);
  fork_execute (objargs[0], objargs, false);
  obstack_free (&argv_obstack, NULL);

  /* Objcopy has created symbols, containing the input file name with
     non-alphanumeric characters replaced by underscores.
     We are going to rename these new symbols.  */
  size_t symbol_name_len = strlen (target_so_filename);
  char *symbol_name = XALLOCAVEC (char, symbol_name_len + 1);
  for (size_t i = 0; i < symbol_name_len; i++)
    {
      char c = target_so_filename[i];
      if (!ISALNUM (c))
	c = '_';
      symbol_name[i] = c;
    }
  symbol_name[symbol_name_len] = '\0';

  char *opt_for_objcopy[3];
  opt_for_objcopy[0] = XALLOCAVEC (char, sizeof ("_binary__start=")
					 + symbol_name_len
					 + strlen (symbols[0]));
  opt_for_objcopy[1] = XALLOCAVEC (char, sizeof ("_binary__end=")
					 + symbol_name_len
					 + strlen (symbols[1]));
  opt_for_objcopy[2] = XALLOCAVEC (char, sizeof ("_binary__size=")
					 + symbol_name_len
					 + strlen (symbols[2]));
  sprintf (opt_for_objcopy[0], "_binary_%s_start=%s", symbol_name, symbols[0]);
  sprintf (opt_for_objcopy[1], "_binary_%s_end=%s", symbol_name, symbols[1]);
  sprintf (opt_for_objcopy[2], "_binary_%s_size=%s", symbol_name, symbols[2]);

  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, "arm-linux-gnueabihf-objcopy");
  obstack_ptr_grow (&argv_obstack, target_so_filename);
  obstack_ptr_grow (&argv_obstack, "--redefine-sym");
  obstack_ptr_grow (&argv_obstack, opt_for_objcopy[0]);
  obstack_ptr_grow (&argv_obstack, "--redefine-sym");
  obstack_ptr_grow (&argv_obstack, opt_for_objcopy[1]);
  obstack_ptr_grow (&argv_obstack, "--redefine-sym");
  obstack_ptr_grow (&argv_obstack, opt_for_objcopy[2]);
  obstack_ptr_grow (&argv_obstack, NULL);

  objargs = XOBFINISH (&argv_obstack, char **);
  fork_execute (objargs[0], objargs, false);
  obstack_free (&argv_obstack, NULL);

  return target_so_filename;
}

int
main (int argc, char **argv)
{
  progname = "hero-mkoffload";
  gcc_init_libintl ();

  // /* Diagnostic -- Start */
  // diagnostic_initialize (global_dc, 0);
  // inform(input_location, "PULP HERO mkoffload start...\n");
  // /* Diagnostic -- End */

  if (atexit (mkoffload_cleanup) != 0)
    fatal_error (input_location, "atexit failed");

  const char *host_compiler = getenv ("COLLECT_GCC");
  if (!host_compiler)
    fatal_error (input_location, "COLLECT_GCC must be set");

  const char *target_driver_name = GCC_INSTALL_NAME;
  char *target_compiler = find_target_compiler (target_driver_name);
  if (target_compiler == NULL)
    fatal_error (input_location, "offload compiler %s not found",
		 target_driver_name);

  /* We may be called with all the arguments stored in some file and
     passed with @file.  Expand them into argv before processing.  */
  expandargv (&argc, &argv);

  /* Diagnostic -- Start */
  // char cmd[1024*4] = "";
  // int i = 0;
  // while(argv[i] != NULL){
  //   strcat(cmd, argv[i]);
  //   strcat(cmd, " ");
  //   i++;
  // }
  // inform(input_location, "%s\n", cmd);
  /* Diagnostic -- End*/

  const char *target_so_filename
    = prepare_target_image (target_compiler, argc, argv);

  const char *host_descr_filename = generate_host_descr_file (host_compiler);

  /* Perform partial linking for the target image and host side descriptor.
     As a result we'll get a finalized object file with all offload data.  */
  struct obstack argv_obstack;
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, "arm-linux-gnueabihf-ld");
  obstack_ptr_grow (&argv_obstack, "-marmelf_linux_eabi");
  obstack_ptr_grow (&argv_obstack, "--relocatable");
  obstack_ptr_grow (&argv_obstack, host_descr_filename);
  obstack_ptr_grow (&argv_obstack, target_so_filename);
  obstack_ptr_grow (&argv_obstack, "-o");
  obstack_ptr_grow (&argv_obstack, out_obj_filename);
  obstack_ptr_grow (&argv_obstack, NULL);

  char **new_argv = XOBFINISH (&argv_obstack, char **);
  /* Diagnostic -- Start */
  // memset(cmd,0,strlen(cmd));
  // i = 0;
  // while(new_argv[i] != NULL){
  //   strcat(cmd, new_argv[i]);
  //   strcat(cmd, " ");
  //   i++;
  // }
  // inform(input_location, "%s\n", cmd);
  /* Diagnostic -- End*/
  fork_execute (new_argv[0], CONST_CAST (char **, new_argv), false);
  obstack_free (&argv_obstack, NULL);

  /* Run objcopy on the resultant object file to localize generated symbols
     to avoid conflicting between different DSO and an executable.  */
  obstack_init (&argv_obstack);
  obstack_ptr_grow (&argv_obstack, "arm-linux-gnueabihf-objcopy");
  obstack_ptr_grow (&argv_obstack, "-L");
  obstack_ptr_grow (&argv_obstack, symbols[0]);
  obstack_ptr_grow (&argv_obstack, "-L");
  obstack_ptr_grow (&argv_obstack, symbols[1]);
  obstack_ptr_grow (&argv_obstack, "-L");
  obstack_ptr_grow (&argv_obstack, symbols[2]);
  obstack_ptr_grow (&argv_obstack, out_obj_filename);
  obstack_ptr_grow (&argv_obstack, NULL);

  new_argv = XOBFINISH (&argv_obstack, char **);      
  fork_execute (new_argv[0], CONST_CAST (char **, new_argv), false);
  obstack_free (&argv_obstack, NULL);

  /* Diagnostic -- Start */
  // inform(input_location, "PULP HERO mkoffload end.\n");
  /* Diagnostic -- End */
  return 0;
}
