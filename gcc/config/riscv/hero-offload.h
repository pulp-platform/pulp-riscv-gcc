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

#ifndef HERO_OFFLOAD_H
#define HERO_OFFLOAD_H

/* Support for OpenACC acc_on_device.  */
#include "gomp-constants.h"

#define ACCEL_COMPILER_acc_device GOMP_DEVICE_PULP_HERO

#endif

