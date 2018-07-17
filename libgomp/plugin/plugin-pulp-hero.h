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

#ifndef PLUGIN_PULP_H
#define PLUGIN_PULP_H

struct plp_nonshm_thread
{
  bool plp_nonshm_exec;
};

//! An Offload Variable descriptor
struct VarDesc {
    //! OffloadItemTypes of source and destination
    union {
        struct {
            uint8_t dst : 4; //!< OffloadItemType of destination
            uint8_t src : 4; //!< OffloadItemType of source
        };
        uint8_t bits;
    } type;

    //! OffloadParameterType that describes direction of data transfer
    union {
        struct {
            uint8_t in  : 1; //!< Set if IN or INOUT
            uint8_t out : 1; //!< Set if OUT or INOUT
        };
        uint8_t bits;
    } direction;

    uint8_t alloc_if;        //!< alloc_if modifier value
    uint8_t free_if;         //!< free_if modifier value
    uint32_t align;          //!< MIC alignment requested for pointer data
    //! Not used by compiler; set to 0
    /*! Used by runtime as offset to data from start of MIC buffer */
    uint32_t mic_offset;
    //! Flags describing this variable
    union {
        struct {
            //! source variable has persistent storage
            uint32_t is_static : 1;
            //! destination variable has persistent storage
            uint32_t is_static_dstn : 1;
            //! has length for c_dv && c_dv_ptr
            uint32_t has_length : 1;
            //! persisted local scalar is in stack buffer
            uint32_t is_stack_buf : 1;
            //! buffer address is sent in data
            uint32_t sink_addr : 1;
            //! alloc displacement is sent in data
            uint32_t alloc_disp : 1;
            //! source data is noncontiguous
            uint32_t is_noncont_src : 1;
            //! destination data is noncontiguous
            uint32_t is_noncont_dst : 1;
        };
        uint32_t bits;
    } flags;
    //! Not used by compiler; set to 0
    /*! Used by runtime as offset to base from data stored in a buffer */
    int64_t offset;
    //! Element byte-size of data to be transferred
    /*! For dope-vector, the size of the dope-vector      */
    int64_t size;
    union {
        //! Set to 0 for array expressions and dope-vectors
        /*! Set to 1 for scalars                          */
        /*! Set to value of length modifier for pointers  */
        int64_t count;
        //! Displacement not used by compiler
        int64_t disp;
    };

    //! This field not used by OpenMP 4.0
    /*! The alloc section expression in #pragma offload   */
    union {
       void *alloc;
       int64_t ptr_arr_offset;
    };

    //! This field not used by OpenMP 4.0
    /*! The into section expression in #pragma offload    */
    /*! For c_data_ptr_array this is the into ptr array   */
    void *into;

    //! For an ordinary variable, address of the variable
    /*! For c_cean_var (C/C++ array expression),
        pointer to arr_desc, which is an array descriptor. */
    /*! For c_data_ptr_array (array of data pointers),
        pointer to ptr_array_descriptor,
        which is a descriptor for pointer array transfers. */
    void *ptr;
};

//! Auxiliary struct used when -g is enabled that holds variable names
struct VarDesc2 {
    const char *sname; //!< Source name
    const char *dname; //!< Destination name (when "into" is used)
};

/*! When the OffloadItemType is c_data_ptr_array
    the ptr field of the main descriptor points to this struct.          */
/*! The type in VarDesc1 merely says c_cean_data_ptr, but the pointer
    type can be c_data_ptr, c_func_ptr, c_void_ptr, or c_string_ptr.
    Therefore the actual pointer type is in the flags field of VarDesc3. */
/*! If flag_align_is_array/flag_alloc_if_is_array/flag_free_if_is_array
    is 0 then alignment/alloc_if/free_if are specified in VarDesc1.      */
/*! If flag_align_is_array/flag_alloc_if_is_array/flag_free_if_is_array
    is 1 then align_array/alloc_if_array/free_if_array specify
    the set of alignment/alloc_if/free_if values.                        */
/*! For the other fields, if neither the scalar nor the array flag
    is set, then that modifier was not specified. If the bits are set
    they specify which modifier was set and whether it was a
    scalar or an array expression.                                       */
struct VarDesc3
{
    void *ptr_array;        //!< Pointer to arr_desc of array of pointers
    void *align_array;      //!< Scalar value or pointer to arr_desc
    void *alloc_if_array;   //!< Scalar value or pointer to arr_desc
    void *free_if_array;    //!< Scalar value or pointer to arr_desc
    void *extent_start;     //!< Scalar value or pointer to arr_desc
    void *extent_elements;  //!< Scalar value or pointer to arr_desc
    void *into_start;       //!< Scalar value or pointer to arr_desc
    void *into_elements;    //!< Scalar value or pointer to arr_desc
    void *alloc_start;      //!< Scalar value or pointer to arr_desc
    void *alloc_elements;   //!< Scalar value or pointer to arr_desc
    /*! Flags that describe the pointer type and whether each field
        is a scalar value or an array expression.        */
    /*! First 6 bits are pointer array element type:
        c_data_ptr, c_func_ptr, c_void_ptr, c_string_ptr */
    /*! Then single bits specify:                        */
    /*!     align_array is an array                      */
    /*!     alloc_if_array is an array                   */
    /*!     free_if_array is an array                    */
    /*!     extent_start is a scalar expression          */
    /*!     extent_start is an array expression          */
    /*!     extent_elements is a scalar expression       */
    /*!     extent_elements is an array expression       */
    /*!     into_start is a scalar expression            */
    /*!     into_start is an array expression            */
    /*!     into_elements is a scalar expression         */
    /*!     into_elements is an array expression         */
    /*!     alloc_start is a scalar expression           */
    /*!     alloc_start is an array expression           */
    /*!     alloc_elements is a scalar expression        */
    /*!     alloc_elements is an array expression        */
    uint32_t array_fields;
};

#endif
