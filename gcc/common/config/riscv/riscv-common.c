/* Common hooks for RISC-V.
   Copyright (C) 2016 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#define _WITH_PULP_CHIP_INFO_FUNCT_

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "common/common-target.h"
#include "common/common-target-def.h"
#include "opts.h"
#include "flags.h"
#include "diagnostic-core.h"

/* Parse a RISC-V ISA string into an option mask.  */

static void
riscv_parse_arch_string (const char *isa, int *flags, location_t loc)
{
//   const char *p = isa;
  char *p = xstrdup (isa);
  char *HeadStr = p;

  for (int i = 0; p[i]; i++) {
	if (p[i]>='a'&& p[i]<='z') {
		p[i] = 'A'+ (p[i]-'a');
	}
  }


  if (Pulp_DP_Format == PULP_DP_FORMAT32) *flags |= MASK_MAP_DOUBLE_TO_FLOAT;

  if (strncmp (p, "RV32", 4) == 0)
    *flags &= ~MASK_64BIT, p += 4;
  else if (strncmp (p, "RV64", 4) == 0)
    *flags |= MASK_64BIT, p += 4;
  else if (*p!='I')
    {
      error_at (loc, "-march=%s: ISA string must begin with rv32 or rv64", isa);
      return;
    }

  if (*p == 'G')
    {
      p++;

      *flags |= MASK_MUL;
      *flags |= MASK_ATOMIC;
      *flags |= MASK_HARD_FLOAT;
      *flags |= MASK_DOUBLE_FLOAT;
    }
  else if (*p == 'I')
    {
      p++;

      *flags &= ~MASK_MUL;
      if (*p == 'M')
	*flags |= MASK_MUL, p++;

      *flags &= ~MASK_ATOMIC;
      if (*p == 'A')
	*flags |= MASK_ATOMIC, p++;

      *flags &= ~(MASK_HARD_FLOAT | MASK_DOUBLE_FLOAT);
      if (*p == 'F')
	{
	  *flags |= MASK_HARD_FLOAT, p++;

	  if (*p == 'D')
	    {
	      *flags |= MASK_DOUBLE_FLOAT;
	      p++;
	    }
	}
    }
  else
    {
      error_at (loc, "-march=%s: invalid ISA string", isa);
      return;
    }

  *flags &= ~MASK_RVC;
  if (*p == 'C')
    *flags |= MASK_RVC, p++;

  if (*p == 'X') {
        int Len;

        switch (PulpDecodeCpu(p+1, &Len)) {
                case PULP_NONE:
                        if (Len==0) {
                                error ("-march=%s: unsupported ISA substring %s", isa, p);
                                return;
                        }
                        break;
                case PULP_RISCV:
                        *flags &= ~MASK_64BIT; *flags |= MASK_MUL; *flags &= ~MASK_ATOMIC;
			riscv_abi = ABI_ILP32;
                        break;
                case PULP_V0:
                        *flags &= ~MASK_64BIT; *flags &= ~MASK_MUL; *flags &= ~MASK_ATOMIC;
			riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_V0) Pulp_Cpu = PULP_V0;
                        else error("-Xpulpv0: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                case PULP_V1:
                        *flags &= ~MASK_64BIT; *flags &= ~MASK_MUL; *flags &= ~MASK_ATOMIC;
			riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_V1) Pulp_Cpu = PULP_V1;
                        else error("-Xpulpv1: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                case PULP_V2:
                        *flags &= ~MASK_64BIT; *flags &= ~MASK_MUL; *flags &= ~MASK_ATOMIC;
                        if (Pulp_DP_Format != PULP_DP_FORMAT32) riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_V2) Pulp_Cpu = PULP_V2;
                        else error("-Xpulpv2: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                case PULP_V3:
                        *flags &= ~MASK_64BIT; *flags |= MASK_MUL; *flags &= ~MASK_ATOMIC;
                        if (Pulp_DP_Format != PULP_DP_FORMAT32) riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_V3) Pulp_Cpu = PULP_V3;
                        else error("-Xpulpv3: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                case PULP_NN:
                        *flags &= ~MASK_64BIT; *flags |= MASK_MUL; *flags &= ~MASK_ATOMIC;
                        if (Pulp_DP_Format != PULP_DP_FORMAT32) riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_NN) Pulp_Cpu = PULP_NN;
                        else error("-XpulpNN: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
/* __GAP8 Start */
                case PULP_GAP8:
                        *flags &= ~MASK_64BIT; *flags |= MASK_MUL; *flags &= ~MASK_ATOMIC;
			riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_GAP8) Pulp_Cpu = PULP_GAP8;
                        else error("-Xgap8: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
/* __GAP8 Stop */
                case PULP_GAP9:
                        *flags &= ~MASK_64BIT; *flags |= MASK_MUL; *flags |= MASK_DIV; *flags &= ~MASK_ATOMIC; *flags |= MASK_HARD_FLOAT; *flags |= MASK_FPREGS_ON_GRREGS; *flags |= MASK_FDIV;
			riscv_abi = ABI_ILP32; Has_F16ALT = 1; Has_F16 = 1; Has_F8 = 1;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_GAP9) Pulp_Cpu = PULP_GAP9;
                        else error("-Xgap9: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                case PULP_SLIM:
                        *flags &= ~MASK_64BIT; *flags &= ~MASK_ATOMIC;
			riscv_abi = ABI_ILP32;
                        if (Pulp_Cpu == PULP_NONE || Pulp_Cpu == PULP_SLIM) Pulp_Cpu = PULP_SLIM;
                        else error("-Xpulpslim: pulp architecture is already defined as %s", PulpProcessorImage(Pulp_Cpu));
                        break;
                default:
                        break;
        }
        p+=(Len+1);
  } else {
        if (Pulp_Cpu != PULP_NONE) {
                *flags &= ~MASK_64BIT; *flags &= ~MASK_ATOMIC;
		riscv_abi = ABI_ILP32;
                *flags &= ~MASK_ATOMIC;
                if (Pulp_Cpu >= PULP_V3)  {
                        *flags |= MASK_MUL;
                } else {
                        *flags &= ~MASK_MUL;
                }
        }
  }


  if (*p)
    {
      error_at (loc, "-march=%s: unsupported ISA substring %qs", isa, p);
      return;
    }
  free (HeadStr);

}

/* Implement TARGET_HANDLE_OPTION.  */

static bool
riscv_handle_option (struct gcc_options *opts,
		     struct gcc_options *opts_set ATTRIBUTE_UNUSED,
		     const struct cl_decoded_option *decoded,
		     location_t loc)
{
  static int Defined = 0;
  switch (decoded->opt_index)
    {
    case OPT_march_:
	if (!Defined) riscv_parse_arch_string (decoded->arg, &opts->x_target_flags, loc);
      return true;

    case OPT_mchip_:
        Defined=0;
        switch (decoded->value) {
                case PULP_CHIP_NONE:
                        break;
                case PULP_CHIP_HONEY:
                        riscv_parse_arch_string ("IXpulpv0",  &opts->x_target_flags, loc); Defined=1;
                        break;
                case PULP_CHIP_PULPINO:
                        riscv_parse_arch_string ("IXpulpv1",  &opts->x_target_flags, loc); Defined=1;
                        break;
/* __GAP8 Start */
                case PULP_CHIP_GAP8:
                        // riscv_parse_arch_string ("IXgap8",  &opts->x_target_flags, loc); Defined=1;
                        riscv_parse_arch_string ("RV32IMCXgap8",  &opts->x_target_flags, loc); Defined=1;
                        break;
/* __GAP8 Stop */
                case PULP_CHIP_GAP9:
                        riscv_parse_arch_string ("RV32IMFCXgap9",  &opts->x_target_flags, loc); Defined=1;
                        break;
                default:
                        break;
        }
        if (Defined) {
                _Pulp_FC = Pulp_Defined_Chips[decoded->value].Pulp_FC;
                _Pulp_PE = Pulp_Defined_Chips[decoded->value].Pulp_PE;
                _Pulp_L2_Size = Pulp_Defined_Chips[decoded->value].Pulp_L2_Size;
                _Pulp_L1_Cluster_Size = Pulp_Defined_Chips[decoded->value].Pulp_L1_Cluster_Size;
                _Pulp_L1_FC_Size = Pulp_Defined_Chips[decoded->value].Pulp_L1_FC_Size;
        }
      return true;
    case OPT_mcpu_:
        error("Use -march to pass pulp cpu info and not -mcpu");
        return true;

    default:
      return true;
    }
}

/* Implement TARGET_OPTION_OPTIMIZATION_TABLE.  */
static const struct default_options riscv_option_optimization_table[] =
  {
    { OPT_LEVELS_1_PLUS, OPT_fsection_anchors, NULL, 1 },
    { OPT_LEVELS_1_PLUS, OPT_fomit_frame_pointer, NULL, 1 },
    { OPT_LEVELS_2_PLUS, OPT_free, NULL, 1 },
    { OPT_LEVELS_NONE, 0, NULL, 0 }
  };

#undef TARGET_OPTION_OPTIMIZATION_TABLE
#define TARGET_OPTION_OPTIMIZATION_TABLE riscv_option_optimization_table

#undef TARGET_HANDLE_OPTION
#define TARGET_HANDLE_OPTION riscv_handle_option

struct gcc_targetm_common targetm_common = TARGETM_COMMON_INITIALIZER;
