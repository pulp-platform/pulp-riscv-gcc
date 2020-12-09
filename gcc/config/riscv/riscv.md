;; Machine description for RISC-V for GNU compiler.
;; Copyright (C) 2011-2017 Free Software Foundation, Inc.
;; Contributed by Andrew Waterman (andrew@sifive.com).
;; Based on MIPS target for GNU compiler.

;; This file is part of GCC.

;; GCC is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GCC is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

(define_c_enum "unspec" [
  ;; Override return address for exception handling.
  UNSPEC_EH_RETURN

  ;; Symbolic accesses.  The order of this list must match that of
  ;; enum riscv_symbol_type in riscv-protos.h.
  UNSPEC_ADDRESS_FIRST
  UNSPEC_PCREL
  UNSPEC_LOAD_GOT
  UNSPEC_TLS
  UNSPEC_TLS_LE
  UNSPEC_TLS_IE
  UNSPEC_TLS_GD

  ;; High part of PC-relative address.
  UNSPEC_AUIPC

  ;; Floating-point unspecs.
  UNSPEC_FLT_QUIET
  UNSPEC_FLE_QUIET
  UNSPEC_COPYSIGN
  UNSPEC_LRINT
  UNSPEC_LROUND

  ;; Stack tie
  UNSPEC_TIE

  ;; Vector permutations
  UNSPEC_VEC_PERM1
  UNSPEC_VEC_PERM2
  UNSPEC_VEC_PERM3
  UNSPEC_VEC_PERM4
  UNSPEC_VEC_PERM5

  ;; Viterbi
  UNSPEC_VIT_MAX
  UNSPEC_VIT_SEL

  ;; Bit manipulation
  UNSPEC_BINS_REG
  UNSPEC_BEXTS_REG
  UNSPEC_BEXTU_REG

  ;; Force read write
  UNSPEC_READSI
  UNSPEC_WRITESI

  ;; Read write CSR
  UNSPEC_SPR_READ
  UNSPEC_SPR_WRITE
  UNSPEC_SPR_BIT_SET
  UNSPEC_SPR_BIT_CLR

  ;; Read write FCSR
  UNSPEC_FCSR_READ
  UNSPEC_FCSR_WRITE

  ;; Nop
  UNSPEC_NOP

  ;; Hardware loops
  UNSPEC_LSETUP_END

  ;; It handlers return
  UNSPEC_ITU
  UNSPEC_ITS
  UNSPEC_ITH
  UNSPEC_ITM

  UNSPEC_READSI_NONVOL

  ;; Mult short sign/unsigned with optional Norm or Norm + round, in operands treated as plain int (short int in an int)
  UNSPEC_MULS
  UNSPEC_MULU
  UNSPEC_MULSN
  UNSPEC_MULSRN
  UNSPEC_MULUN
  UNSPEC_MULURN

  UNSPEC_MACS
  UNSPEC_MACU
  UNSPEC_MACSN
  UNSPEC_MACSRN
  UNSPEC_MACUN
  UNSPEC_MACURN

  ;; To force type conversion without explicit cast
  UNSPEC_TRUNCSIHI
  UNSPEC_TRUNCSIQI

  UNSPEC_BITREV

])

(define_c_enum "unspecv" [
  ;; Register save and restore.
  UNSPECV_GPR_SAVE
  UNSPECV_GPR_RESTORE

  ;; Floating-point unspecs.
  UNSPECV_FRFLAGS
  UNSPECV_FSFLAGS

  ;; Blockage and synchronization.
  UNSPECV_BLOCKAGE
  UNSPECV_FENCE
  UNSPECV_FENCE_I

  ;; Hardware loops
  UNSPECV_ALLOC
  UNSPECV_LC_SET

  ;; Read event unit
  UNSPECV_READ_EVU

  ;; Load Base + Offset
  UNSPECV_OFFSETED_READ
  UNSPECV_OFFSETED_READ_HALF
  UNSPECV_OFFSETED_READ_BYTE
  UNSPECV_OFFSETED_READ_OMP
  UNSPECV_OFFSETED_WRITE
  UNSPECV_OFFSETED_WRITE_HALF
  UNSPECV_OFFSETED_WRITE_BYTE

  ;; OpenMP experimental
  UNSPECV_OMP_PULP_BARRIER
  UNSPECV_OMP_PULP_CRITICAL_START
  UNSPECV_OMP_PULP_CRITICAL_END

  ;; Forced read write, volatile
  UNSPECV_WRITESI_VOL
  UNSPECV_READSI_VOL

  ;; Read write CSR
  UNSPECV_SPR_READ_VOL

])

(define_constants
  [(RETURN_ADDR_REGNUM		1)
   (T0_REGNUM			5)
   (T1_REGNUM			6)
   (S0_REGNUM			8)
   (S1_REGNUM			9)
   (S2_REGNUM			18)
   (REG_LC0                     66)
   (REG_LC1                     67)
   (REG_LE0                     68)
   (REG_LE1                     69)
   (REG_LS0                     70)
   (REG_LS1                     71)
   (VIT_REG                     72)
])

(include "predicates.md")
(include "constraints.md")

;; ....................
;;
;;	Attributes
;;
;; ....................

(define_attr "got" "unset,xgot_high,load"
  (const_string "unset"))

;; Classification of moves, extensions and truncations.  Most values
;; are as for "type" (see below) but there are also the following
;; move-specific values:
;;
;; andi		a single ANDI instruction
;; shift_shift	a shift left followed by a shift right
;;
;; This attribute is used to determine the instruction's length and
;; scheduling type.  For doubleword moves, the attribute always describes
;; the split instructions; in some cases, it is more appropriate for the
;; scheduling type to be "multi" instead.
(define_attr "move_type"
  "unknown,load,fpload,store,fpstore,mtc,mfc,move,fmove,
   const,logical,arith,andi,shift_shift"
  (const_string "unknown"))

;; Main data type used by the insn
(define_attr "mode" "unknown,none,QI,HI,SI,DI,TI,HF,OHF,SF,DF,TF,V2HI,V4QI,V2HF,V2OHF"
  (const_string "unknown"))

;; True if the main data type is twice the size of a word.
(define_attr "dword_mode" "no,yes"
  (cond [(and (eq_attr "mode" "DI,DF")
	      (eq (symbol_ref "TARGET_64BIT") (const_int 0)))
	 (const_string "yes")

	 (and (eq_attr "mode" "TI,TF")
	      (ne (symbol_ref "TARGET_64BIT") (const_int 0)))
	 (const_string "yes")]
	(const_string "no")))

;; Classification of each insn.
;; branch	conditional branch
;; jump		unconditional jump
;; call		unconditional call
;; load		load instruction(s)
;; fpload	floating point load
;; store	store instruction(s)
;; fpstore	floating point store
;; mtc		transfer to coprocessor
;; mfc		transfer from coprocessor
;; const	load constant
;; arith	integer arithmetic instructions
;; logical      integer logical instructions
;; shift	integer shift instructions
;; slt		set less than instructions
;; imul		integer multiply
;; idiv		integer divide
;; move		integer register move (addi rd, rs1, 0)
;; fmove	floating point register move
;; fadd		floating point add/subtract
;; fmul		floating point multiply
;; fmadd	floating point multiply-add
;; fdiv		floating point divide
;; fcmp		floating point compare
;; fcvt		floating point convert
;; fsqrt	floating point square root
;; multi	multiword sequence (or user asm statements)
;; nop		no operation
;; ghost	an instruction that produces no real code
(define_attr "type"
  "unknown,branch,jump,call,load,fpload,store,fpstore,
   mtc,mfc,const,arith,logical,shift,slt,imul,idiv,move,fmove,fadd,fmul,
   fmadd,fdiv,fcmp,fcvt,fsqrt,multi,nop,ghost,qnt"
  (cond [(eq_attr "got" "load") (const_string "load")

	 ;; If a doubleword move uses these expensive instructions,
	 ;; it is usually better to schedule them in the same way
	 ;; as the singleword form, rather than as "multi".
	 (eq_attr "move_type" "load") (const_string "load")
	 (eq_attr "move_type" "fpload") (const_string "fpload")
	 (eq_attr "move_type" "store") (const_string "store")
	 (eq_attr "move_type" "fpstore") (const_string "fpstore")
	 (eq_attr "move_type" "mtc") (const_string "mtc")
	 (eq_attr "move_type" "mfc") (const_string "mfc")

	 ;; These types of move are always single insns.
	 (eq_attr "move_type" "fmove") (const_string "fmove")
	 (eq_attr "move_type" "arith") (const_string "arith")
	 (eq_attr "move_type" "logical") (const_string "logical")
	 (eq_attr "move_type" "andi") (const_string "logical")

	 ;; These types of move are always split.
	 (eq_attr "move_type" "shift_shift")
	   (const_string "multi")

	 ;; These types of move are split for doubleword modes only.
	 (and (eq_attr "move_type" "move,const")
	      (eq_attr "dword_mode" "yes"))
	   (const_string "multi")
	 (eq_attr "move_type" "move") (const_string "move")
	 (eq_attr "move_type" "const") (const_string "const")]
	(const_string "unknown")))

;; Length of instruction in bytes.
(define_attr "length" ""
   (cond [
	  ;; Branches further than +/- 4 KiB require two instructions.
	  (eq_attr "type" "branch")
	  (if_then_else (and (le (minus (match_dup 0) (pc)) (const_int 4088))
				  (le (minus (pc) (match_dup 0)) (const_int 4092)))
	  (const_int 4)
	  (const_int 8))

	  ;; Conservatively assume calls take two instructions (AUIPC + JALR).
	  ;; The linker will opportunistically relax the sequence to JAL.
	  (eq_attr "type" "call") (const_int 8)

	  ;; "Ghost" instructions occupy no space.
	  (eq_attr "type" "ghost") (const_int 0)

	  (eq_attr "got" "load") (const_int 8)

	  (eq_attr "type" "fcmp") (const_int 8)

	  ;; SHIFT_SHIFTs are decomposed into two separate instructions.
	  (eq_attr "move_type" "shift_shift")
		(const_int 8)

	  ;; Check for doubleword moves that are decomposed into two
	  ;; instructions.
	  (and (eq_attr "move_type" "mtc,mfc,move")
	       (eq_attr "dword_mode" "yes"))
	  (const_int 8)

	  ;; Doubleword CONST{,N} moves are split into two word
	  ;; CONST{,N} moves.
	  (and (eq_attr "move_type" "const")
	       (eq_attr "dword_mode" "yes"))
	  (symbol_ref "riscv_split_const_insns (operands[1]) * 4")

	  ;; Otherwise, constants, loads and stores are handled by external
	  ;; routines.
	  (eq_attr "move_type" "load,fpload")
	  (symbol_ref "riscv_load_store_insns (operands[1], insn) * 4")
	  (eq_attr "move_type" "store,fpstore")
	  (symbol_ref "riscv_load_store_insns (operands[0], insn) * 4")
	  ] (const_int 4)))

;; Is copying of this instruction disallowed?
(define_attr "cannot_copy" "no,yes" (const_string "no"))

;; Describe a user's asm statement.
(define_asm_attributes
  [(set_attr "type" "multi")])

;; This mode iterator allows 32-bit and 64-bit GPR patterns to be generated
;; from the same template.
(define_mode_iterator GPR [SI (DI "TARGET_64BIT")])

;; This mode iterator allows :P to be used for patterns that operate on
;; pointer-sized quantities.  Exactly one of the two alternatives will match.
(define_mode_iterator P [(SI "Pmode == SImode") (DI "Pmode == DImode")])

;; Likewise, but for XLEN-sized quantities.
(define_mode_iterator X [(SI "!TARGET_64BIT") (DI "TARGET_64BIT")])

;; Branches operate on XLEN-sized quantities, but for RV64 we accept
;; QImode values so we can force zero-extension.
(define_mode_iterator BR [(QI "TARGET_64BIT") SI (DI "TARGET_64BIT")])

;; 32-bit moves for which we provide move patterns.
(define_mode_iterator MOVE32 [SI])

(define_mode_iterator MODE_PULP [V4QI V2HI (V2HF "Has_F16") (V2OHF "Has_F16ALT") (OHF "Has_F16ALT") SF SI])

;; 64-bit modes for which we provide move patterns.
(define_mode_iterator MOVE64 [DI DF])

;; Iterator for sub-32-bit integer modes.
(define_mode_iterator SHORT_ALL [QI HI])
(define_mode_iterator SHORT [HI])

(define_mode_iterator SUBDISF [QI HI (HF "(Has_F16)") (OHF "(Has_F16ALT)") SI (SF "(!TARGET_HARD_FLOAT || TARGET_FPREGS_ON_GRREGS)") V2HI (V2HF "(Has_F16)") (V2OHF "(Has_F16ALT)") V4QI])
(define_mode_iterator SUBDI [QI HI SI])

;; Iterator for HImode constant generation.
(define_mode_iterator HISI [HI SI])

;; Iterator for QImode extension patterns.
(define_mode_iterator SUPERQI [HI SI (DI "TARGET_64BIT")])

;; Iterator for extending loads.
(define_mode_iterator ZERO_EXTEND_LOAD [QI HI (SI "TARGET_64BIT")])

;; Iterator for hardware integer modes narrower than XLEN.
(define_mode_iterator SUBX [QI HI (SI "TARGET_64BIT")])

;; Iterator for hardware-supported integer modes.
(define_mode_iterator ANYI [QI HI SI (DI "TARGET_64BIT")])

;; Iterator for hardware-supported floating-point modes.
(define_mode_iterator STDF [(SF "TARGET_HARD_FLOAT")
                            (DF "TARGET_DOUBLE_FLOAT")])

(define_mode_iterator ANYF [(SF "TARGET_HARD_FLOAT")
			    (DF "TARGET_DOUBLE_FLOAT")
                            (HF "(TARGET_HARD_FLOAT&&Has_F16)")
                            (OHF "(TARGET_HARD_FLOAT&&Has_F16ALT)")])

;; Iterator for hardware-supported floating-point modes.
(define_mode_iterator ANYFULLF [(SF "TARGET_HARD_FLOAT")
			        (DF "TARGET_DOUBLE_FLOAT")])
;; Like ANYF, but only applies to scalar modes.
(define_mode_iterator SCALARF [(SF "TARGET_HARD_FLOAT")
                               (DF "TARGET_DOUBLE_FLOAT")
                               (HF "(TARGET_HARD_FLOAT&&Has_F16)")
                               (OHF "(TARGET_HARD_FLOAT&&Has_F16ALT)")])

;; Iterator for hardware-supported small floating-point modes.
(define_mode_iterator SMALLF [(V1SF "TARGET_HARD_FLOAT")
                              (HF "(TARGET_HARD_FLOAT&&Has_F16)")
                              (OHF "(TARGET_HARD_FLOAT&&Has_F16ALT)")])


(define_mode_attr size_mem   [(V4QI "4") (V2HI "4") (V2HF "4") (V2OHF "4") (SF "4") (SI "4") (HI "2") (HF "2") (OHF "2") (QI "1")])
(define_mode_attr size_load_store [(V4QI "w") (V2HI "w") (V2HF "w") (V2OHF "w") (SF "w") (SI "w") (QI "b") (HI "h") (HF "h") (OHF "h")])

;; This attribute gives the length suffix for a sign- or zero-extension
;; instruction.
(define_mode_attr size [(QI "b") (HI "h")])

;; Mode attributes for loads.
(define_mode_attr load [(QI "lb") (HI "lh") (HF "lh") (OHF "lh") (SI "lw") (DI "ld") (SF "flw") (DF "fld")])

;; Instruction names for stores.
(define_mode_attr store [(QI "sb") (HI "sh") (HF "sh") (OHF "sh") (SI "sw") (DI "sd") (SF "fsw") (DF "fsd")])

;; This attribute gives the best constraint to use for registers of
;; a given mode.
(define_mode_attr reg [(SI "d") (DI "d") (CC "d")])

;; This attribute gives the format suffix for floating-point operations.
(define_mode_attr fmt [(V1SF "s") (SF "s") (DF "d") (HF "h") (OHF "ah")])

;; This attribute gives the integer suffix for floating-point conversions.
(define_mode_attr ifmt [(SI "w") (DI "l") (V1SF "w") (V2HF "x") (V2OHF "x") ])

;; This attribute gives the format suffix for atomic memory operations.
(define_mode_attr amo [(SI "w") (DI "d")])

;; This attribute gives the upper-case mode name for one unit of a
;; floating-point mode.
(define_mode_attr UNITMODE [(V1SF "V1SF") (HF "HF") (OHF "OHF") (SF "SF") (DF "DF")])

;; This attribute gives the integer mode that has half the size of
;; the controlling mode.
(define_mode_attr HALFMODE [(DF "SI") (DI "SI") (TF "DI")])

(define_mode_attr LDSTMODE [(SI "SI") (HI "HI") (QI "QI")])

(define_mode_attr LDSTINDMODE [(V4QI "V4QI") (V2HI "V2HI") (V2HF "V2HF") (V2OHF "V2OHF") (SF "SF") (SI "SI") (HI "HI") (HF "HF") (OHF "OHF") (QI "QI")])

;; Iterator and attributes for floating-point rounding instructions.
(define_int_iterator RINT [UNSPEC_LRINT UNSPEC_LROUND])
(define_int_attr rint_pattern [(UNSPEC_LRINT "rint") (UNSPEC_LROUND "round")])
(define_int_attr rint_rm [(UNSPEC_LRINT "dyn") (UNSPEC_LROUND "rmm")])

;; Iterator and attributes for quiet comparisons.
(define_int_iterator QUIET_COMPARISON [UNSPEC_FLT_QUIET UNSPEC_FLE_QUIET])
(define_int_attr quiet_pattern [(UNSPEC_FLT_QUIET "lt") (UNSPEC_FLE_QUIET "le")])

;; This code iterator allows signed and unsigned widening multiplications
;; to use the same template.
(define_code_iterator any_extend [sign_extend zero_extend])

(define_code_attr su_mod     [(sign_extend "s") (zero_extend "u")])
(define_code_attr su_mod_alt [(sign_extend "") (zero_extend "u")])

;; This code iterator is used for operations followed by rounding and normalization
(define_code_iterator norm_op [ashiftrt lshiftrt])
(define_code_attr norm_sign   [(ashiftrt "") (lshiftrt "u")])

;; This code iterator allows the two right shift instructions to be
;; generated from the same template.
(define_code_iterator any_shiftrt [ashiftrt lshiftrt])

;; This code iterator allows the three shift instructions to be generated
;; from the same template.
(define_code_iterator any_shift [ashift ashiftrt lshiftrt])

;; This code iterator allows the three bitwise instructions to be generated
;; from the same template.
(define_code_iterator any_bitwise [and ior xor])

;; This code iterator allows unsigned and signed division to be generated
;; from the same template.
(define_code_iterator any_div [div udiv mod umod])

;; This code iterator allows unsigned and signed modulus to be generated
;; from the same template.
(define_code_iterator any_mod [mod umod])

;; These code iterators allow the signed and unsigned scc operations to use
;; the same template.
(define_code_iterator any_gt [gt gtu])
(define_code_iterator any_ge [ge geu])
(define_code_iterator any_lt [lt ltu])
(define_code_iterator any_le [le leu])

;; <u> expands to an empty string when doing a signed operation and
;; "u" when doing an unsigned operation.
(define_code_attr u [(sign_extend "") (zero_extend "u")
		     (gt "") (gtu "u")
		     (ge "") (geu "u")
		     (lt "") (ltu "u")
		     (le "") (leu "u")])

;; <su> is like <u>, but the signed form expands to "s" rather than "".
(define_code_attr su [(sign_extend "s") (zero_extend "u")])

;; <optab> expands to the name of the optab for a particular code.
(define_code_attr optab [(ashift "ashl")
			 (ashiftrt "ashr")
			 (lshiftrt "lshr")
			 (div "div")
			 (mod "mod")
			 (udiv "udiv")
			 (umod "umod")
			 (ge "ge")
			 (le "le")
			 (gt "gt")
			 (lt "lt")
			 (ior "ior")
			 (xor "xor")
			 (and "and")
			 (plus "add")
			 (minus "sub")])

;; <insn> expands to the name of the insn that implements a particular code.
(define_code_attr insn [(ashift "sll")
			(ashiftrt "sra")
			(lshiftrt "srl")
			(div "div")
			(mod "rem")
			(udiv "divu")
			(umod "remu")
			(ior "or")
			(xor "xor")
			(and "and")
			(plus "add")
			(minus "sub")])

;; Ghost instructions produce no real code and introduce no hazards.
;; They exist purely to express an effect on dataflow.
(define_insn_reservation "ghost" 0
  (eq_attr "type" "ghost")
  "nothing")

;;
;;  ....................
;;
;;	ADDITION
;;
;;  ....................
;;

(define_insn "add<mode>3"
  [(set (match_operand:ANYF            0 "register_operand" "=f")
	(plus:ANYF (match_operand:ANYF 1 "register_operand" " f")
		   (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fadd.s\t%0,%1,%2" : "fadd.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fadd")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "addsi3"
  [(set (match_operand:SI          0 "register_operand" "=r,r")
	(plus:SI (match_operand:SI 1 "register_operand" " r,r")
		 (match_operand:SI 2 "arith_operand"    " r,I")))]
  ""
  { return TARGET_64BIT ? "addw\t%0,%1,%2" : "add\t%0,%1,%2"; }
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

(define_insn "adddi3"
  [(set (match_operand:DI          0 "register_operand" "=r,r")
	(plus:DI (match_operand:DI 1 "register_operand" " r,r")
		 (match_operand:DI 2 "arith_operand"    " r,I")))]
  "TARGET_64BIT"
  "add\t%0,%1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "DI")])

(define_insn "*addsi3_extended"
  [(set (match_operand:DI               0 "register_operand" "=r,r")
	(sign_extend:DI
	     (plus:SI (match_operand:SI 1 "register_operand" " r,r")
		      (match_operand:SI 2 "arith_operand"    " r,I"))))]
  "TARGET_64BIT"
  "addw\t%0,%1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

(define_insn "*addsi3_extended2"
  [(set (match_operand:DI                       0 "register_operand" "=r,r")
	(sign_extend:DI
	  (subreg:SI (plus:DI (match_operand:DI 1 "register_operand" " r,r")
			      (match_operand:DI 2 "arith_operand"    " r,I"))
		     0)))]
  "TARGET_64BIT"
  "addw\t%0,%1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	SUBTRACTION
;;
;;  ....................
;;

(define_insn "sub<mode>3"
  [(set (match_operand:ANYF             0 "register_operand" "=f")
	(minus:ANYF (match_operand:ANYF 1 "register_operand" " f")
		    (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fsub.s\t%0,%1,%2" : "fsub.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fadd")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "subdi3"
  [(set (match_operand:DI 0            "register_operand" "= r")
	(minus:DI (match_operand:DI 1  "reg_or_0_operand" " rJ")
		   (match_operand:DI 2 "register_operand" "  r")))]
  "TARGET_64BIT"
  "sub\t%0,%z1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "DI")])

(define_insn "subsi3"
  [(set (match_operand:SI           0 "register_operand" "= r")
	(minus:SI (match_operand:SI 1 "reg_or_0_operand" " rJ")
		  (match_operand:SI 2 "register_operand" "  r")))]
  ""
  { return TARGET_64BIT ? "subw\t%0,%z1,%2" : "sub\t%0,%z1,%2"; }
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

(define_insn "*subsi3_extended"
  [(set (match_operand:DI               0 "register_operand" "= r")
	(sign_extend:DI
	    (minus:SI (match_operand:SI 1 "reg_or_0_operand" " rJ")
		      (match_operand:SI 2 "register_operand" "  r"))))]
  "TARGET_64BIT"
  "subw\t%0,%z1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

(define_insn "*subsi3_extended2"
  [(set (match_operand:DI                        0 "register_operand" "=r")
	(sign_extend:DI
	  (subreg:SI (minus:DI (match_operand:DI 1 "reg_or_0_operand" " r")
			       (match_operand:DI 2 "register_operand" " r"))
		     0)))]
  "TARGET_64BIT"
  "subw\t%0,%z1,%2"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	MULTIPLICATION
;;
;;  ....................
;;

(define_insn "mul<mode>3"
  [(set (match_operand:ANYF               0 "register_operand" "=f")
	(mult:ANYF (match_operand:ANYF    1 "register_operand" " f")
		      (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmul.s\t%0,%1,%2" : "fmul.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fmul")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "mulsi3"
  [(set (match_operand:SI          0 "register_operand" "=r")
	(mult:SI (match_operand:SI 1 "register_operand" " r")
		 (match_operand:SI 2 "register_operand" " r")))]
  "(Pulp_Cpu>=PULP_V0) || TARGET_MUL || (Pulp_Cpu==PULP_SLIM) || Pulp_Cpu==PULP_IMG"
  {
        if (TARGET_64BIT) return "mulw\t%0,%1,%2";
        else if (Pulp_Cpu) return "p.mul\t%0,%1,%2";
        else return "mul\t%0,%1,%2";
  }
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")])

(define_insn "muldi3"
  [(set (match_operand:DI          0 "register_operand" "=r")
	(mult:DI (match_operand:DI 1 "register_operand" " r")
		 (match_operand:DI 2 "register_operand" " r")))]
  "TARGET_MUL && TARGET_64BIT"
  "mul\t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "DI")])

(define_insn "*mulsi3_extended"
  [(set (match_operand:DI              0 "register_operand" "=r")
	(sign_extend:DI
	    (mult:SI (match_operand:SI 1 "register_operand" " r")
		     (match_operand:SI 2 "register_operand" " r"))))]
  "TARGET_MUL && TARGET_64BIT"
  "mulw\t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")])

(define_insn "*mulsi3_extended2"
  [(set (match_operand:DI                       0 "register_operand" "=r")
	(sign_extend:DI
	  (subreg:SI (mult:DI (match_operand:DI 1 "register_operand" " r")
			      (match_operand:DI 2 "register_operand" " r"))
		     0)))]
  "TARGET_MUL && TARGET_64BIT"
  "mulw\t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")])

;;
;;  ........................
;;
;;	MULTIPLICATION HIGH-PART
;;
;;  ........................
;;


(define_expand "<u>mulditi3"
  [(set (match_operand:TI                         0 "register_operand")
	(mult:TI (any_extend:TI (match_operand:DI 1 "register_operand"))
		 (any_extend:TI (match_operand:DI 2 "register_operand"))))]
  "TARGET_MUL && TARGET_64BIT"
{
  rtx low = gen_reg_rtx (DImode);
  emit_insn (gen_muldi3 (low, operands[1], operands[2]));

  rtx high = gen_reg_rtx (DImode);
  emit_insn (gen_<u>muldi3_highpart (high, operands[1], operands[2]));

  emit_move_insn (gen_lowpart (DImode, operands[0]), low);
  emit_move_insn (gen_highpart (DImode, operands[0]), high);
  DONE;
})

(define_insn "<u>muldi3_highpart"
  [(set (match_operand:DI                0 "register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (any_extend:TI
		       (match_operand:DI 1 "register_operand" " r"))
		     (any_extend:TI
		       (match_operand:DI 2 "register_operand" " r")))
	    (const_int 64))))]
  "TARGET_MUL && TARGET_64BIT"
  "mulh<u>\t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "DI")])

(define_expand "usmulditi3"
  [(set (match_operand:TI                          0 "register_operand")
	(mult:TI (zero_extend:TI (match_operand:DI 1 "register_operand"))
		 (sign_extend:TI (match_operand:DI 2 "register_operand"))))]
  "TARGET_MUL && TARGET_64BIT"
{
  rtx low = gen_reg_rtx (DImode);
  emit_insn (gen_muldi3 (low, operands[1], operands[2]));

  rtx high = gen_reg_rtx (DImode);
  emit_insn (gen_usmuldi3_highpart (high, operands[1], operands[2]));

  emit_move_insn (gen_lowpart (DImode, operands[0]), low);
  emit_move_insn (gen_highpart (DImode, operands[0]), high);
  DONE;
})

(define_insn "usmuldi3_highpart"
  [(set (match_operand:DI                0 "register_operand" "=r")
	(truncate:DI
	  (lshiftrt:TI
	    (mult:TI (zero_extend:TI
		       (match_operand:DI 1 "register_operand"  "r"))
		     (sign_extend:TI
		       (match_operand:DI 2 "register_operand" " r")))
	    (const_int 64))))]
  "TARGET_MUL && TARGET_64BIT"
  "mulhsu\t%0,%2,%1"
  [(set_attr "type" "imul")
   (set_attr "mode" "DI")])

(define_expand "<u>mulsidi3"
  [(set (match_operand:DI            0 "register_operand" "=r")
	(mult:DI (any_extend:DI
		   (match_operand:SI 1 "register_operand" " r"))
		 (any_extend:DI
		   (match_operand:SI 2 "register_operand" " r"))))]
  "(TARGET_MUL||(Pulp_Cpu>=PULP_V2)||(Pulp_Cpu==PULP_SLIM)||(Pulp_Cpu==PULP_IMG)) && !TARGET_64BIT"
{
  rtx temp = gen_reg_rtx (SImode);
  emit_insn (gen_mulsi3 (temp, operands[1], operands[2]));
  emit_insn (gen_<u>mulsi3_highpart (riscv_subword (operands[0], true),
				     operands[1], operands[2]));
  emit_insn (gen_movsi (riscv_subword (operands[0], false), temp));
  DONE;
})

(define_insn "<u>mulsi3_highpart"
  [(set (match_operand:SI                0 "register_operand" "=r")
	(truncate:SI
	  (lshiftrt:DI
	    (mult:DI (any_extend:DI
		       (match_operand:SI 1 "register_operand" " r"))
		     (any_extend:DI
		       (match_operand:SI 2 "register_operand" " r")))
	    (const_int 32))))]
  "(TARGET_MUL||(Pulp_Cpu>=PULP_V2)||(Pulp_Cpu==PULP_SLIM)||(Pulp_Cpu==PULP_IMG)) && !TARGET_64BIT"
  {
        if (Pulp_Cpu) return "p.mulh<u>\t%0,%1,%2";
        else return "mulh<u>\t%0,%1,%2";
  }
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")])


(define_expand "usmulsidi3"
  [(set (match_operand:DI            0 "register_operand" "=r")
	(mult:DI (zero_extend:DI
		   (match_operand:SI 1 "register_operand" " r"))
		 (sign_extend:DI
		   (match_operand:SI 2 "register_operand" " r"))))]
  "(TARGET_MUL||(Pulp_Cpu>=PULP_V2)||(Pulp_Cpu==PULP_SLIM)||(Pulp_Cpu==PULP_IMG)) && !TARGET_64BIT"
{
  rtx temp = gen_reg_rtx (SImode);
  emit_insn (gen_mulsi3 (temp, operands[1], operands[2]));
  emit_insn (gen_usmulsi3_highpart (riscv_subword (operands[0], true),
				     operands[1], operands[2]));
  emit_insn (gen_movsi (riscv_subword (operands[0], false), temp));
  DONE;
})

(define_insn "usmulsi3_highpart"
  [(set (match_operand:SI                0 "register_operand" "=r")
	(truncate:SI
	  (lshiftrt:DI
	    (mult:DI (zero_extend:DI
		       (match_operand:SI 1 "register_operand" " r"))
		     (sign_extend:DI
		       (match_operand:SI 2 "register_operand" " r")))
	    (const_int 32))))]
  "(TARGET_MUL||(Pulp_Cpu>=PULP_V2)||(Pulp_Cpu==PULP_SLIM)||(Pulp_Cpu==PULP_IMG)) && !TARGET_64BIT"
  {
        if (Pulp_Cpu) return "p.mulhsu\t%0,%2,%1";
        else return "mulhsu\t%0,%2,%1";
  }
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	DIVISION and REMAINDER
;;
;;  ....................
;;

(define_insn "<optab>si3"
  [(set (match_operand:SI             0 "register_operand" "=r")
	(any_div:SI (match_operand:SI 1 "register_operand" " r")
		    (match_operand:SI 2 "register_operand" " r")))]
  "(TARGET_DIV || ((Pulp_Cpu >= PULP_V2)||(Pulp_Cpu==PULP_SLIM)||(Pulp_Cpu==PULP_IMG)))"
  { return TARGET_64BIT ? "<insn>w\t%0,%1,%2" : Pulp_Cpu?"p.<insn>\t%0,%1,%2":"<insn>\t%0,%1,%2"; }

  [(set_attr "type" "idiv")
   (set_attr "mode" "SI")])

(define_insn "<optab>di3"
  [(set (match_operand:DI             0 "register_operand" "=r")
	(any_div:DI (match_operand:DI 1 "register_operand" " r")
		    (match_operand:DI 2 "register_operand" " r")))]
  "TARGET_DIV && TARGET_64BIT"
  "<insn>\t%0,%1,%2"
  [(set_attr "type" "idiv")
   (set_attr "mode" "DI")])

(define_insn "*<optab>si3_extended"
  [(set (match_operand:DI                 0 "register_operand" "=r")
	(sign_extend:DI
	    (any_div:SI (match_operand:SI 1 "register_operand" " r")
			(match_operand:SI 2 "register_operand" " r"))))]
  "TARGET_DIV && TARGET_64BIT"
  "<insn>w\t%0,%1,%2"
  [(set_attr "type" "idiv")
   (set_attr "mode" "DI")])

(define_insn "div<mode>3"
  [(set (match_operand:ANYF           0 "register_operand" "=f")
	(div:ANYF (match_operand:ANYF 1 "register_operand" " f")
		  (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT && TARGET_FDIV"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fdiv.s\t%0,%1,%2" : "fdiv.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fdiv")
   (set_attr "mode" "<UNITMODE>")])

;;
;;  ....................
;;
;;	SQUARE ROOT
;;
;;  ....................

(define_insn "sqrt<mode>2"
  [(set (match_operand:ANYF            0 "register_operand" "=f")
	(sqrt:ANYF (match_operand:ANYF 1 "register_operand" " f")))]
  "TARGET_HARD_FLOAT && TARGET_FDIV"
{
    return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fsqrt.s\t%0,%1" : "fsqrt.<fmt>\t%0,%1";
}
  [(set_attr "type" "fsqrt")
   (set_attr "mode" "<UNITMODE>")])

;; Floating point multiply accumulate instructions.

;; a * b + c
(define_insn "fma<mode>4"
  [(set (match_operand:ANYF           0 "register_operand" "=f")
	(fma:ANYF (match_operand:ANYF 1 "register_operand" " f")
		  (match_operand:ANYF 2 "register_operand" " f")
		  (match_operand:ANYF 3 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmadd.s\t%0,%1,%2,%3" : "fmadd.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; a * b - c
(define_insn "fms<mode>4"
  [(set (match_operand:ANYF                     0 "register_operand" "=f")
	(fma:ANYF (match_operand:ANYF           1 "register_operand" " f")
		  (match_operand:ANYF           2 "register_operand" " f")
		  (neg:ANYF (match_operand:ANYF 3 "register_operand" " f"))))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmsub.s\t%0,%1,%2,%3" : "fmsub.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -a * b - c
(define_insn "fnms<mode>4"
  [(set (match_operand:ANYF               0 "register_operand" "=f")
	(fma:ANYF
	    (neg:ANYF (match_operand:ANYF 1 "register_operand" " f"))
	    (match_operand:ANYF           2 "register_operand" " f")
	    (neg:ANYF (match_operand:ANYF 3 "register_operand" " f"))))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fnmadd.s\t%0,%1,%2,%3" : "fnmadd.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -a * b + c
(define_insn "fnma<mode>4"
  [(set (match_operand:ANYF               0 "register_operand" "=f")
	(fma:ANYF
	    (neg:ANYF (match_operand:ANYF 1 "register_operand" " f"))
	    (match_operand:ANYF           2 "register_operand" " f")
	    (match_operand:ANYF           3 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fnmsub.s\t%0,%1,%2,%3" : "fnmsub.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -(-a * b - c), modulo signed zeros
(define_insn "*fma<mode>4"
  [(set (match_operand:ANYF                   0 "register_operand" "=f")
	(neg:ANYF
	    (fma:ANYF
		(neg:ANYF (match_operand:ANYF 1 "register_operand" " f"))
		(match_operand:ANYF           2 "register_operand" " f")
		(neg:ANYF (match_operand:ANYF 3 "register_operand" " f")))))]
  "TARGET_HARD_FLOAT && !HONOR_SIGNED_ZEROS (<MODE>mode)"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmadd.s\t%0,%1,%2,%3" : "fmadd.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -(-a * b + c), modulo signed zeros
(define_insn "*fms<mode>4"
  [(set (match_operand:ANYF                   0 "register_operand" "=f")
	(neg:ANYF
	    (fma:ANYF
		(neg:ANYF (match_operand:ANYF 1 "register_operand" " f"))
		(match_operand:ANYF           2 "register_operand" " f")
		(match_operand:ANYF           3 "register_operand" " f"))))]
  "TARGET_HARD_FLOAT && !HONOR_SIGNED_ZEROS (<MODE>mode)"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmsub.s\t%0,%1,%2,%3" : "fmsub.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -(a * b + c), modulo signed zeros
(define_insn "*fnms<mode>4"
  [(set (match_operand:ANYF         0 "register_operand" "=f")
	(neg:ANYF
	    (fma:ANYF
		(match_operand:ANYF 1 "register_operand" " f")
		(match_operand:ANYF 2 "register_operand" " f")
		(match_operand:ANYF 3 "register_operand" " f"))))]
  "TARGET_HARD_FLOAT && !HONOR_SIGNED_ZEROS (<MODE>mode)"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fnmadd.s\t%0,%1,%2,%3" : "fnmadd.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])

;; -(a * b - c), modulo signed zeros
(define_insn "*fnma<mode>4"
  [(set (match_operand:ANYF                   0 "register_operand" "=f")
	(neg:ANYF
	    (fma:ANYF
		(match_operand:ANYF           1 "register_operand" " f")
		(match_operand:ANYF           2 "register_operand" " f")
		(neg:ANYF (match_operand:ANYF 3 "register_operand" " f")))))]
  "TARGET_HARD_FLOAT && !HONOR_SIGNED_ZEROS (<MODE>mode)"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fnmsub.s\t%0,%1,%2,%3" : "fnmsub.<fmt>\t%0,%1,%2,%3"; }
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<UNITMODE>")])


;; f32 = smallfloat*smallfloat
(define_insn "mul<SMALLF:mode>sf3"
  [(set (match_operand:SF     0 "register_operand" "=f")
        (mult:SF
          (float_extend:SF (match_operand:SMALLF 1 "register_operand" "xf"))
          (float_extend:SF (match_operand:SMALLF 2 "register_operand" "xf"))
        )
  )]
  "TARGET_HARD_FLOAT && Has_FAUX && (<MODE>mode == OHFmode && Has_F16ALT)"
  "fmulex.s.<fmt>\t%0,%1,%2"
  [(set_attr "type" "fmadd")
   (set_attr "mode" "SF")])


;; f32 += smallfloat*smallfloat
(define_insn "madd<SMALLF:mode>sf3_internal"
  [(set (match_operand:SF  0 "register_operand" "+f")
        (fma:SF (match_operand:SMALLF 1 "register_operand" "xf")
                (match_operand:SMALLF 2 "register_operand" "xf")
                (match_dup 0))
  )]
  "TARGET_HARD_FLOAT && Has_FAUX && (<MODE>mode == OHFmode && Has_F16ALT)"
  "fmacex.s.<fmt>\t%0,%1,%2"
  [(set_attr "type" "fmadd")
   (set_attr "mode" "SF")])

;; f32 = smallfloat*smallfloat + f32
(define_expand "madd<SMALLF:mode>sf4"
  [(set (match_operand:SF  0 "register_operand" " ")
        (fma:SF (match_operand:SMALLF 1 "register_operand" " ")
                (match_operand:SMALLF 2 "register_operand" " ")
                (match_operand:SF     3 "register_operand" " "))
  )]
  "TARGET_HARD_FLOAT && Has_FAUX && (<MODE>mode == OHFmode && Has_F16ALT)"
  {
    emit_insn(gen_movsf(operands[0], operands[3]));
    emit_insn(gen_madd<SMALLF:mode>sf3_internal(operands[0], operands[1], operands[2]));
    DONE;
  }
)

;;
;;  ....................
;;
;;	SIGN INJECTION
;;
;;  ....................

(define_insn "abs<mode>2"
  [(set (match_operand:ANYF           0 "register_operand" "=f")
	(abs:ANYF (match_operand:ANYF 1 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fabs.s\t%0,%1" : "fabs.<fmt>\t%0,%1"; }
  [(set_attr "type" "fmove")
   (set_attr "mode" "<UNITMODE>")])

;; Pulp Only
(define_insn "abssi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (abs:SI (match_operand:SI 1 "register_operand" "r")))]
  "(Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG)"
  "p.abs\t%0,%1"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")])


(define_insn "copysign<mode>3"
  [(set (match_operand:ANYF 0 "register_operand"               "=f")
	(unspec:ANYF [(match_operand:ANYF 1 "register_operand" " f")
		      (match_operand:ANYF 2 "register_operand" " f")]
		     UNSPEC_COPYSIGN))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fsgnj.s\t%0,%1,%2" : "fsgnj.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fmove")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "neg<mode>2"
  [(set (match_operand:ANYF           0 "register_operand" "=f")
	(neg:ANYF (match_operand:ANYF 1 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fneg.s\t%0,%1" : "fneg.<fmt>\t%0,%1"; }
  [(set_attr "type" "fmove")
   (set_attr "mode" "<UNITMODE>")])

;;
;;  ....................
;;
;;	MIN/MAX
;;
;;  ....................

(define_insn "smin<mode>3"
  [(set (match_operand:ANYF            0 "register_operand" "=f")
	(smin:ANYF (match_operand:ANYF 1 "register_operand" " f")
		   (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmin.s\t%0,%1,%2" : "fmin.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fmove")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "smax<mode>3"
  [(set (match_operand:ANYF            0 "register_operand" "=f")
	(smax:ANYF (match_operand:ANYF 1 "register_operand" " f")
		   (match_operand:ANYF 2 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "fmax.s\t%0,%1,%2" : "fmax.<fmt>\t%0,%1,%2"; }
  [(set_attr "type" "fmove")
   (set_attr "mode" "<UNITMODE>")])

;; Pulp Only

(define_insn "sminsi3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (smin:SI (match_operand:SI 1 "register_operand" "r,r")
                 (match_operand:SI 2 "nonmemory_operand" "r,J")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOMINMAX)"
"@
 p.min \t%0,%1,%2\t# signed min
 p.min \t%0,%1,x0\t# signed min 0"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI")]
)


(define_insn "smaxsi3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (smax:SI (match_operand:SI 1 "register_operand" "r,r")
                 (match_operand:SI 2 "nonmemory_operand" "r,J")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOMINMAX)"
"@
 p.max \t%0,%1,%2\t# signed max
 p.max \t%0,%1,x0\t# signed max 0"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI")]
)

(define_insn "uminsi3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (umin:SI (match_operand:SI 1 "register_operand" "r")
                 (match_operand:SI 2 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOMINMAX)"
"p.minu \t%0,%1,%2\t# unsigned min"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "umaxsi3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (umax:SI (match_operand:SI 1 "register_operand" "r")
                 (match_operand:SI 2 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOMINMAX)"
"p.maxu \t%0,%1,%2\t# signed max"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;      AVG, AVGU
;;
;;  ....................

(define_insn "avgsi3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI (match_operand:SI 1 "register_operand" "r")
                         (match_operand:SI 2 "reg_or_0_operand" "rJ"))
                (const_int 1)
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOMINMAX)"
{ return (Pulp_Cpu >= PULP_V2) ? "p.addN \t%0,%1,%z2,1" : "p.avg \t%0,%1,%z2"; }
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgusi3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI (match_operand:SI 1 "register_operand" "r")
                         (match_operand:SI 2 "reg_or_0_operand" "rJ"))
                (const_int 1)
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOMINMAX)"
{ return (Pulp_Cpu >= PULP_V2) ? "p.adduN \t%0,%1,%z2,1" : "p.avgu \t%0,%1,%z2"; }
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;      BIT MANIPULATION
;;
;;  ....................

(define_insn "popcountsi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (popcount:SI (match_operand:SI 1 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"p.cnt \t%0,%1\t# count bit set to 1"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "clrsbsi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (clrsb:SI (match_operand:SI 1 "register_operand" "r"))
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"p.clb \t%0, %1\t # count leading bits, int"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "fl1si2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (minus:SI (const_int 31)
                  (clz:SI (match_operand:SI 1 "register_operand" "r"))
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"p.fl1 \t%0,%1\t# position of first set bit from msb"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_expand "clzsi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (clz:SI (match_operand:SI 1 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"
{
        rtx reg = gen_reg_rtx (SImode);

        emit_insn (gen_rtx_SET (reg, gen_rtx_CONST_INT(SImode, 31)));
        emit_insn (gen_fl1si2(operands[0], operands[1]));
        emit_insn (gen_subsi3(operands[0], reg, operands[0]));
        DONE;
}"
)

(define_insn "ctzsi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ctz:SI (match_operand:SI 1 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"p.ff1 \t%0,%1\t# position of first set bit from lsb"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_expand "paritysi2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (parity:SI (match_operand:SI 1 "register_operand" "r"))
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
"
{
        emit_insn (gen_popcountsi2(operands[0], operands[1]));
        emit_insn (gen_extzvsi(operands[0], operands[0], gen_rtx_CONST_INT(SImode, 1), gen_rtx_CONST_INT(SImode, 0)));
        DONE;
}"
)

;;
;;  ....................
;;
;;      ROTATE RIGHT
;;
;;  ....................

(define_insn "rotrsi3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (rotatert:SI (match_operand:SI 1 "register_operand" "r")
                     (match_operand:SI 2 "register_operand" "r")))]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOBITOP)"
  "p.ror \t%0,%1,%2\t# rotate"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	PARTIAL PRODUCTS (16x16 into 32)
;;
;;  ....................

;; Standard gcc patterns

(define_insn "truncsihi2"
  [(set (match_operand:HI 0 "register_operand" "=r") (unspec:HI [(match_operand:SI 1 "register_operand" "0")] UNSPEC_TRUNCSIHI))]
  ""
  ""
  [(set_attr "type"	"nop")
   (set_attr "mode"	"none")]
)

(define_insn "truncsiqi2"
  [(set (match_operand:QI 0 "register_operand" "=r") (unspec:QI [(match_operand:SI 1 "register_operand" "0")] UNSPEC_TRUNCSIQI))]
  ""
  ""
  [(set_attr "type"	"nop")
   (set_attr "mode"	"none")]
)

(define_insn "<su_mod_alt>mul<SHORT:mode>si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (mult:SI (any_extend:SI (match_operand:SHORT 1 "register_operand" "r"))
                 (any_extend:SI (match_operand:SHORT 2 "register_operand" "r")))
   )]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
"p.mul<su_mod> \t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

;; Pure builtins mults/multu, purpose is to use plain int arguments without casting to short int
(define_insn "mulsForced_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec:SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r")] UNSPEC_MULS)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.muls \t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "muluForced_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r")] UNSPEC_MULU)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.mulu \t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "smulhi3_highpart"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                         (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                )
                (const_int 16)
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.mulsN \t%0,%1,%2,16\t # mul16x16 into 32 with right shift 16"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "umulhi3_highpart"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (mult:SI (zero_extend:SI (match_operand:HI 1 "register_operand" "r"))
                         (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                )
                (const_int 16)
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.muluN \t%0,%1,%2,16\t # uns mul16x16 into 32 with right logical shift 16"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

;; Non standard gcc patterns

(define_insn "mulhhs_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                 (ashiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.mulhhs \t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulhhu_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                 (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
  "p.mulhhu \t%0,%1,%2"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	PARTIAL MULT (16x16 into 32) WITH NORM AND ROUNDING
;;
;;  ....................

(define_insn "mulsNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                         (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.mulsN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulsRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                 (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "(!TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.mulsRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)



(define_insn "mulsRNr_hi3"
  [(set (match_operand:HI 0 "register_operand" "=r")
	(truncate:HI
        	(ashiftrt:SI
                	(plus:SI
                        	(mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                 	 (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                        	)
                        	(match_operand:SI 4 "immediate_operand" "i")
                	)
                	(match_operand:SI 3 "immediate_operand" "i")
        	)
	)
   )
  ]
  "(!TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 15))"
  "p.mulsRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)




(define_insn "muluNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (mult:SI (zero_extend:SI (match_operand:HI 1 "register_operand" "r"))
                         (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.muluN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "muluRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (mult:SI (zero_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                 (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.muluRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

;; Pure builtins mults/multu with norm an doptional rounding, purpose is to use plain int arguments without casting to short int
(define_insn "mulsForcedNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "immediate_operand" "i")] UNSPEC_MULSN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.mulsN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulsForcedRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "immediate_operand" "i") (match_operand:SI 4 "immediate_operand" "i")] UNSPEC_MULSRN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.mulsRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "muluForcedNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "immediate_operand" "i")] UNSPEC_MULUN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.muluN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "muluForcedRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "immediate_operand" "i") (match_operand:SI 4 "immediate_operand" "i")] UNSPEC_MULURN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.muluRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulhhsNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                         (ashiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.mulhhsN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulhhuNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                         (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.mulhhuN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulhhsRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                 (ashiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.mulhhsRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "mulhhuRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                 (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.mulhhuRN \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)


;;
;;  ....................
;;
;;	PARTIAL MAC (16x16 into 32)
;;
;;  ....................

(define_insn "macs<mode>_si4"
  [(set (match_operand:SI 0 "register_operand" "=a,r")
        (plus:SI (mult:SI (sign_extend:SI (match_operand:SHORT 1 "register_operand" "r,r"))
                          (sign_extend:SI (match_operand:SHORT 2 "register_operand" "r,r"))
                 )
                 (match_operand:SI 3 "register_operand" "r,0")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "@
   p.macs \t%0,%1,%2,%3
   p.macs \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "mode" "SI")]
)

(define_insn "macu<mode>_si4"
  [(set (match_operand:SI 0 "register_operand" "=a,r")
        (plus:SI (mult:SI (zero_extend:SI (match_operand:SHORT 1 "register_operand" "r,r"))
                          (zero_extend:SI (match_operand:SHORT 2 "register_operand" "r,r"))
                 )
                 (match_operand:SI 3 "register_operand" "r,0")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "@
   p.macu \t%0,%1,%2,%3
   p.macu \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "mode" "SI")]
)


;; Pure builtins macs/macu, purpose is to use plain int arguments without casting to short int
(define_insn "macsForced_si3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "register_operand" "r,r") (match_operand:SI 3 "register_operand" "r,0")] UNSPEC_MACS)
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOMAC)"
  "@
   p.macs \t%0,%1,%2,%3
   p.macs \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "mode" "SI")]
)

(define_insn "macuForced_si3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "register_operand" "r,r") (match_operand:SI 3 "register_operand" "r,0")] UNSPEC_MACU)
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOMAC)"
  "@
   p.macu \t%0,%1,%2,%3
   p.macu \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "mode" "SI")]
)


(define_insn "machlsu_si4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (plus:SI (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                          (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                 )
                 (match_operand:SI 3 "register_operand" "r")
        )
   )
  ]
  "((Pulp_Cpu==PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "p.machlsu \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machlu_si4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (plus:SI (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                          (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                 )
                 (match_operand:SI 3 "register_operand" "r")
        )
   )
  ]
  "((Pulp_Cpu==PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "p.machlu \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machhs_si4"
  [(set (match_operand:SI 0 "register_operand" "=a,r")
        (plus:SI (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r,r") (const_int 16))
                          (ashiftrt:SI (match_operand:SI 2 "register_operand" "r,r") (const_int 16))
                 )
                 (match_operand:SI 3 "register_operand" "r,0")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "@
   p.machhs \t%0,%1,%2,%3
   p.machhs \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "length" "1")]
)

(define_insn "machhu_si4"
  [(set (match_operand:SI 0 "register_operand" "=a,r")
        (plus:SI (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r,r") (const_int 16))
                          (lshiftrt:SI (match_operand:SI 2 "register_operand" "r,r") (const_int 16))
                 )
                 (match_operand:SI 3 "register_operand" "r,0")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "@
   p.machhu \t%0,%1,%2,%3
   p.machhu \t%0,%1,%2"
  [(set_attr "type" "imul,imul")
   (set_attr "mode" "SI")]
)

(define_insn "machls_si4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (plus:SI (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                          (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                 )
                 (match_operand:SI 3 "register_operand" "r")
        )
   )
  ]
  "((Pulp_Cpu==PULP_V0) && !TARGET_MASK_NOPARTMAC)"
  "p.machls \t%0,%1,%2,%3"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)


;;
;;  ....................
;;
;;	PARTIAL MAC (16x16 into 32) WITH ROUNDING AND NORM
;;
;;  ....................


(define_insn "macsNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                 (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                        )
                        (match_operand:SI 3 "register_operand" "0")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.macsN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "macuNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (mult:SI (zero_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                 (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                        )
                        (match_operand:SI 3 "register_operand" "0")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.macuN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)


;; Pure builtins macs/macu with Norm and optional rounding, purpose is to use plain int arguments without casting to short int
(define_insn "macsForcedNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec:SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "register_operand" "0") (match_operand:SI 4 "immediate_operand" "i")] UNSPEC_MACSN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.macsN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "macsForcedRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "register_operand" "0")
		     (match_operand:SI 4 "immediate_operand" "i") (match_operand:SI 5 "immediate_operand" "i")] UNSPEC_MACSRN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.macsRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "macuForcedNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "register_operand" "0") (match_operand:SI 4 "immediate_operand" "i")] UNSPEC_MACUN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.macuN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "macuForcedRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec: SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "register_operand" "r") (match_operand:SI 3 "register_operand" "0")
		     (match_operand:SI 4 "immediate_operand" "i") (match_operand:SI 5 "immediate_operand" "i")] UNSPEC_MACURN)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.macuRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)


(define_insn "macsRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (plus:SI
                                (mult:SI (sign_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                         (sign_extend:SI (match_operand:HI 2 "register_operand" "r"))
                                )
                                (match_operand:SI 3 "register_operand" "0")
                        )
                        (match_operand:SI 5 "immediate_operand" "i")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.macsRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "macuRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (plus:SI
                                (mult:SI (zero_extend:SI (match_operand:HI 1 "register_operand" "r"))
                                         (zero_extend:SI (match_operand:HI 2 "register_operand" "r"))
                                )
                                (match_operand:SI 3 "register_operand" "0")
                        )
                        (match_operand:SI 5 "immediate_operand" "i")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.macuRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machhsNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                 (ashiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                        )
                        (match_operand:SI 3 "register_operand" "0")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.machhsN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machhuNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                 (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                        )
                        (match_operand:SI 3 "register_operand" "0")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], NULL, 31))"
  "p.machhuN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machhsRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ashiftrt:SI
                (plus:SI
                        (plus:SI
                                (mult:SI (ashiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                         (ashiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                                )
                                (match_operand:SI 3 "register_operand" "0")
                        )
                        (match_operand:SI 5 "immediate_operand" "i")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.machhsRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)

(define_insn "machhuRNr_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (lshiftrt:SI
                (plus:SI
                        (plus:SI
                                (mult:SI (lshiftrt:SI (match_operand:SI 1 "register_operand" "r") (const_int 16))
                                         (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 16))
                                )
                                (match_operand:SI 3 "register_operand" "0")
                        )
                        (match_operand:SI 5 "immediate_operand" "i")
                )
                (match_operand:SI 4 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMULMACNORMROUND && riscv_valid_norm_round_imm_op(operands[4], operands[5], 31))"
  "p.machhuRN \t%0,%1,%2,%4"
  [(set_attr "type" "imul")
   (set_attr "mode" "SI")]
)




;;
;;  ....................
;;
;;	MAC (32x32 into 32)
;;
;;  ....................

(define_insn "maddsisi4"
  [(set (match_operand:SI 0 "register_operand" "=a,r")
        (plus:SI (mult:SI (match_operand:SI 1 "register_operand" "r,r")
                          (match_operand:SI 2 "register_operand" "r,r"))
                 (match_operand:SI 3 "register_operand" "r,0"))
   )
  ]
"((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOMAC)"
"@
 p.mac \t%0,%1,%2,%3\t# mac 32x32 in 32 instruction
 p.mac \t%0,%1,%2\t# mac 32x32 in 32 instruction"
[(set_attr "type" "imul,imul")
 (set_attr "mode" "SI")]
)

(define_insn "msubsisi4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (minus:SI (match_operand:SI 3 "register_operand" "0")
		  (mult:SI (match_operand:SI 1 "register_operand" "r")
                           (match_operand:SI 2 "register_operand" "r"))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOMAC)"
"p.msu \t%0,%1,%2\t# mac 32x32 in 32 instruction"
[(set_attr "type" "imul")
 (set_attr "mode" "SI")]
)


;;
;;  ....................
;;
;;	ADD/SUB WITH ROUNDING AND NORM
;;
;;  ....................

(define_insn "addN<norm_sign>_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (match_operand:SI 1 "register_operand" "r")
                        (match_operand:SI 2 "reg_or_0_operand" "rJ")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.add<norm_sign>N \t%0,%1,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "addN<norm_sign>_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "reg_or_0_operand" "rJ")
                )
                (match_operand:SI 3 "register_operand" "r")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND)"
  "p.add<norm_sign>Nr \t%0,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "subN<norm_sign>_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (minus:SI
                        (match_operand:SI 1 "register_operand" "r")
                        (match_operand:SI 2 "reg_or_0_operand" "rJ")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND && riscv_valid_norm_round_imm_op(operands[3], NULL, 31))"
  "p.sub<norm_sign>N \t%0,%1,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "subN<norm_sign>_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (minus:SI
                        (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "reg_or_0_operand" "rJ")
                )
                (match_operand:SI 3 "register_operand" "r")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND)"
  "p.sub<norm_sign>Nr \t%0,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "addRN<norm_sign>_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (plus:SI
                                (match_operand:SI 1 "register_operand" "r")
                                (match_operand:SI 2 "reg_or_0_operand" "rJ")
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.add<norm_sign>RN \t%0,%1,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "addRN<norm_sign>_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (plus:SI (match_operand:SI 1 "register_operand" "0")
                                 (match_operand:SI 2 "reg_or_0_operand" "rJ")
                        )
			(ashift:SI (const_int 1)
				   (minus:SI (match_operand:SI 3 "register_operand" "r") (const_int 1))
				   ; (minus:SI (match_operand:SI 3 "nonmemory_operand" "r,i") (const_int 1))
			)
                )
                (match_dup 3)
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND)"
  "p.add<norm_sign>RNr \t%0,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "subRN<norm_sign>_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (minus:SI
                                (match_operand:SI 1 "register_operand" "r")
                                (match_operand:SI 2 "reg_or_0_operand" "rJ")
                        )
                        (match_operand:SI 4 "immediate_operand" "i")
                )
                (match_operand:SI 3 "immediate_operand" "i")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND && riscv_valid_norm_round_imm_op(operands[3], operands[4], 31))"
  "p.sub<norm_sign>RN \t%0,%1,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "subRN<norm_sign>_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (norm_op:SI
                (plus:SI
                        (minus:SI
                                (match_operand:SI 1 "register_operand" "0")
                                (match_operand:SI 2 "reg_or_0_operand" "rJ")
                        )
			(ashift:SI (const_int 1)
				   (minus:SI (match_operand:SI 3 "register_operand" "r") (const_int 1))
			)
                )
                (match_dup 3)
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOADDSUBNORMROUND)"
  "p.sub<norm_sign>RNr \t%0,%z2,%3"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	CLIP/CLIPU
;;
;;  ....................

(define_insn "clip_maxmin"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smax:SI (smin:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "immediate_operand" "i"))
                 (match_operand:SI 3 "immediate_operand" "i")))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP && riscv_valid_clip_operands (operands[2], operands[3], 1)"
  "p.clip\\t%0,%1,%B2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "clip_minmax"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smin:SI (smax:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "immediate_operand" "i"))
                 (match_operand:SI 3 "immediate_operand" "i")))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP && riscv_valid_clip_operands (operands[3], operands[2], 1)"
  "p.clip\\t%0,%1,%B3"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn"clip_minmax_reg"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smin:SI (smax:SI (match_operand:SI 1 "register_operand" "r")
			  (neg:SI (plus:SI (match_operand:SI 2 "register_operand" "r") (const_int 1)))
		 )
		 (match_dup 2)))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP"
  "p.clipr\\t%0,%1,%2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)


(define_insn"clip_maxmin_reg"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smax:SI (smin:SI (match_operand:SI 1 "register_operand" "r")
			  (match_operand:SI 2 "register_operand" "r")
		 )
		 (neg:SI (plus:SI (match_dup 2) (const_int 1)))))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP"
  "p.clipr\\t%0,%1,%2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "clipu_maxmin"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smax:SI (smin:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "immediate_operand" "i"))
                 (match_operand:SI 3 "immediate_operand" "i")))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP && riscv_valid_clip_operands (operands[2], operands[3], 0)"
  "p.clipu\\t%0,%1,%B2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "clipu_minmax"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smin:SI (smax:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "immediate_operand" "i"))
                 (match_operand:SI 3 "immediate_operand" "i")))]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP && riscv_valid_clip_operands (operands[3], operands[2], 0)"
  "p.clipu\\t%0,%1,%B3"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "clipu_maxmin_reg"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smax:SI (smin:SI (match_operand:SI 1 "register_operand" "r")
                          (match_operand:SI 2 "register_operand" "r")
		 )
		 (const_int 0)
        )
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP"
  "p.clipur\\t%0,%1,%2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "clipu_minmax_reg"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (smin:SI (smax:SI (match_operand:SI 1 "register_operand" "r") (const_int 0))
		 (match_operand:SI 2 "register_operand" "r")
        )
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOCLIP"
  "p.clipur\\t%0,%1,%2"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	BIT INSERT/EXTRACT/EXTRACTU/SET/CLEAR
;;
;;  ....................

(define_insn "bclrsi3"
  [(set	(match_operand:SI 0 "register_operand" "=r")
	(and:SI	(match_operand:SI 1 "register_operand" "r")
		(match_operand:SI 2 "immediate_operand" "i")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP && riscv_valid_bit_field_imm_operand(operands[2], NULL, 0, NULL, NULL))"
{
	int Offset, Size;
	rtx xoperands[5];

	(void) riscv_valid_bit_field_imm_operand(operands[2], NULL, 0, &Size, &Offset);

	xoperands[0] = operands[0];
	xoperands[1] = operands[1];
	xoperands[2] = operands[2];
	xoperands[3] = gen_rtx_CONST_INT (SImode, Size-1);
	xoperands[4] = gen_rtx_CONST_INT (SImode, Offset);
	output_asm_insn("p.bclr \t%0,%1,%3,%4 # Bit clear", xoperands);
	return "";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;; Size: R2[9..5], Offset: R2[4..0]
;; R0 = R1 & ~((1<<((R2>>5)&0x1F)-1)<<(R2&0x1F)
(define_insn "bclrsi3_reg"
  [(set	(match_operand:SI 0 "register_operand" "=r")
	(and:SI	(match_operand:SI 1 "register_operand" "r")
		(not:SI (ashift:SI
				(minus:SI
					(ashift:SI (const_int 1)
						   (plus:SI
					   	   	(and:SI (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 5)) (const_int 31))
							(const_int 1)
						   )
					)
					(const_int 1)
				)
				(and:SI (match_dup 2) (const_int 31))
			)
		)
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
  "p.bclrr\\t%0,%1,%2 # Bit clear reg"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "bsetsi3"
  [(set	(match_operand:SI 0 "register_operand" "=r")
	(ior:SI	(match_operand:SI 1 "register_operand" "r")
		(match_operand:SI 2 "immediate_operand" "i")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP && riscv_valid_bit_field_imm_operand(operands[2], NULL, 1, NULL, NULL))"
{
	int Offset, Size;
	rtx xoperands[5];

	(void) riscv_valid_bit_field_imm_operand(operands[2], NULL, 1, &Size, &Offset);
	xoperands[0] = operands[0];
	xoperands[1] = operands[1];
	xoperands[2] = operands[2];
	xoperands[3] = gen_rtx_CONST_INT (SImode, Size-1);
	xoperands[4] = gen_rtx_CONST_INT (SImode, Offset);
	output_asm_insn("p.bset \t%0,%1,%3,%4 # Bit set", xoperands);
	return "";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;; Size: R2[9..5], Offset: R2[4..0]
;; R0 = R1 | ((1<<((R2>>5)&0x1F)-1)<<(R2&0x1F)
(define_insn "bsetsi3_reg"
  [(set	(match_operand:SI 0 "register_operand" "=r")
	(ior:SI	(match_operand:SI 1 "register_operand" "r")
		(ashift:SI
			(minus:SI
				(ashift:SI (const_int 1)
					   (plus:SI
				   	   	(and:SI (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 5)) (const_int 31))
						(const_int 1)
					   )
				)
				(const_int 1)
			)
			(and:SI (match_dup 2) (const_int 31))
		)
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
  "p.bsetr\\t%0,%1,%2 # Bit set reg"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "extvsi"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (sign_extract:SI (match_operand:SI 1 "register_operand" "r")
                         (match_operand:SI 2 "immediate_operand" "i")
                         (match_operand:SI 3 "immediate_operand" "i")))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
	operands[2] = GEN_INT(INTVAL(operands[2])-1);
 	return "p.extract \t%0,%1,%2,%3 # Bit extract signed";
}
  [(set_attr "type" "logical")
   (set_attr "length" "1")]
)


;; Size: R2[9..5], Offset: R2[4..0]
(define_insn "bextracts_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (sign_extract:SI (match_operand:SI 1 "register_operand" "r")
			 (plus:SI (and:SI (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 5)) (const_int 31))
				  (const_int 1))
			 (and:SI (match_dup 2) (const_int 31))
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
  "p.extractr \t%0,%1,%2 # Bit extract signed, arg reg"
  [(set_attr "type" "logical")
   (set_attr "length" "1")]
)

;; Size: R3[9..5], Offset: R3[4..0]
(define_insn "bextracts_reg_alt_si3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
		    (match_operand:SI 2 "nonmemory_operand" "r,i")] UNSPEC_BEXTS_REG)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
  if (which_alternative == 0) {
  	return "p.extractr \t%0,%1,%2 # Bit extract signed, arg reg";
  } else {
	rtx xoperands[4];
	HOST_WIDE_INT Mask = INTVAL(operands[2]);

	xoperands[0] = operands[0]; xoperands[1] =
	xoperands[2] = gen_rtx_CONST_INT (SImode, (Mask>>5)&0x1F);
	xoperands[3] = gen_rtx_CONST_INT (SImode, (Mask)&0x1F);
	output_asm_insn("p.extract\t%0,%1,%2,%3 # Bit extract signed", xoperands);
	return "";
  }
}
[(set_attr "type" "logical,logical")
 (set_attr "mode" "SI")]
)

;; Size: R3[9..5], Offset: R3[4..0]
(define_insn "bextractu_reg_alt_si3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec:SI [(match_operand:SI 1 "register_operand" "r,r")
		    (match_operand:SI 2 "nonmemory_operand" "r,i")] UNSPEC_BEXTU_REG)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
  if (which_alternative == 0) {
  	return "p.extractur \t%0,%1,%2 # Bit extract unsigned, reg arg";
  } else {
	rtx xoperands[4];
	HOST_WIDE_INT Mask = INTVAL(operands[2]);

	xoperands[0] = operands[0]; xoperands[1] =
	xoperands[2] = gen_rtx_CONST_INT (SImode, (Mask>>5)&0x1F);
	xoperands[3] = gen_rtx_CONST_INT (SImode, (Mask)&0x1F);
	output_asm_insn("p.extractu\t%0,%1,%2,%3 # Bit extract unsigned", xoperands);
	return "";
  }
}
[(set_attr "type" "logical,logical")
 (set_attr "mode" "SI")]
)

(define_insn "extzvsi"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extract:SI (match_operand:SI 1 "register_operand" "r")
                         (match_operand:SI 2 "immediate_operand" "i")
                         (match_operand:SI 3 "immediate_operand" "i")))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
	operands[2] = GEN_INT(INTVAL(operands[2])-1);
  	return "p.extractu \t%0,%1,%2,%3 # Bit extract unsigned";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;; Size: R2[9..5], Offset: R2[4..0]
(define_insn "bextractu_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extract:SI (match_operand:SI 1 "register_operand" "r")
			 (plus:SI (and:SI (lshiftrt:SI (match_operand:SI 2 "register_operand" "r") (const_int 5)) (const_int 31))
				  (const_int 1))
			 (and:SI (match_dup 2) (const_int 31))
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
  "p.extractur \t%0,%1,%2 # Bit extract unsigned, reg arg"
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "insvsi"
  [(set (zero_extract:SI (match_operand:SI 0 "register_operand" "+r")
                         (match_operand:SI 1 "immediate_operand" "i")
                         (match_operand:SI 2 "immediate_operand" "i"))
        (match_operand:SI 3 "reg_or_0_operand" "rJ")
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
	operands[1] = GEN_INT(INTVAL(operands[1])-1);
  	if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  		return "p.insert\t%0,x0,%1,%2";
  	else return "p.insert\t%0,%3,%1,%2";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "*insvsi_internal1"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (and:SI (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "immediate_operand" "i"))
                (and:SI (match_operand:SI 3 "reg_or_0_operand" "rJ")
                        (match_operand:SI 4 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP) && riscv_bottom_bitmask_p (INTVAL (operands[4]))
   && INTVAL(operands[2]) == ~INTVAL(operands[4])"
{
  int len, pos;
  pos = riscv_bitmask (INTVAL (operands[4]), &len, SImode);
  operands[2] = GEN_INT (pos);
  operands[4] = GEN_INT (len-1);
  if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  	return "p.insert\t%0,x0,%4,%2";
  else return "p.insert\t%0,%3,%4,%2";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "*insvsi_internal2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (and:SI (match_operand:SI 1 "reg_or_0_operand" "rJ")
                        (match_operand:SI 2 "immediate_operand" "i"))
                (and:SI (match_operand:SI 3 "register_operand" "0")
                        (match_operand:SI 4 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP) && riscv_bottom_bitmask_p (INTVAL (operands[2]))
   && INTVAL(operands[2]) == ~INTVAL(operands[4])"
{
  int len, pos;
  pos = riscv_bitmask (INTVAL (operands[2]), &len, SImode);
  operands[2] = GEN_INT (pos);
  operands[4] = GEN_INT (len-1);
  if (operands[1] == CONST0_RTX (GET_MODE (operands[1])))
  	return "p.insert\t%0,x0,%4,%2";
  else return "p.insert\t%0,%1,%4,%2";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "invsipat1"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (and:SI (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "immediate_operand" "i"))
                (and:SI (ashift:SI (match_operand:SI 3 "reg_or_0_operand" "rJ")
			           (match_operand:SI 5 "immediate_operand" "i"))
                        (match_operand:SI 4 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)
   && riscv_bitmask (INTVAL (operands[4]), NULL, VOIDmode) == INTVAL (operands[5])
   && INTVAL(operands[2]) == ~INTVAL(operands[4])"
{
  int len;
  riscv_bitmask (INTVAL (operands[4]), &len, SImode);
  operands[4] = GEN_INT (len-1);
  if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  	return "p.insert\t%0,x0,%4,%5";
  else return "p.insert\t%0,%3,%4,%5";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;; Size: R3[9..5], Offset: R3[4..0]
(define_insn "binsert_reg_si3"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec:SI [(match_operand:SI 1 "register_operand" "0,0")
		    (match_operand:SI 2 "reg_or_0_operand" "rJ,rJ")
		    (match_operand:SI 3 "nonmemory_operand" "r,i")] UNSPEC_BINS_REG)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)"
{
  if (which_alternative == 0) {
  	return "p.insertr\t%0,%z2,%3";
  } else {
	rtx xoperands[5];
	HOST_WIDE_INT Mask = INTVAL(operands[3]);

	xoperands[0] = operands[0]; xoperands[1] = operands[1]; xoperands[2] = operands[2];
	xoperands[3] = gen_rtx_CONST_INT (SImode, (Mask>>5)&0x1F);
	xoperands[4] = gen_rtx_CONST_INT (SImode, (Mask)&0x1F);
	output_asm_insn("p.insert\t%0,%z2,%3,%4", xoperands);
	return "";
  }
}
[(set_attr "type" "logical,logical")
 (set_attr "mode" "SI")]
)

(define_insn "*insvsi_internal4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (and:SI (ashift:SI (match_operand:SI 3 "reg_or_0_operand" "rJ")
				   (match_operand:SI 5 "immediate_operand" "i"))
                        (match_operand:SI 4 "immediate_operand" "i"))
	 	(and:SI (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP)
   && riscv_bitmask (INTVAL (operands[4]), NULL, VOIDmode) == INTVAL (operands[5])
   && INTVAL(operands[2]) == ~INTVAL(operands[4])"
{
  int len;
  riscv_bitmask (INTVAL (operands[4]), &len, SImode);
  operands[4] = GEN_INT (len-1);
  if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  	return "p.insert\t%0,x0,%4,%5";
  else return "p.insert\t%0,%3,%4,%5";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "*insvsi_internal5"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (and:SI (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "immediate_operand" "i"))
                (ashift:SI (match_operand:SI 3 "reg_or_0_operand" "rJ")
			   (match_operand:SI 4 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP) && riscv_bitmask_ins_p (INTVAL (operands[2]), INTVAL (operands[4]), SImode)"
{
  int len;
  riscv_bitmask (~INTVAL (operands[2]), &len, SImode);
  operands[2] = GEN_INT (len-1);
  if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  	return "p.insert\t%0,x0,%2,%4";
  else return "p.insert\t%0,%3,%2,%4";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

(define_insn "*insvsi_internal4"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (ior:SI (ashift:SI (match_operand:SI 3 "reg_or_0_operand" "rJ")
			   (match_operand:SI 4 "immediate_operand" "i"))
		(and:SI (match_operand:SI 1 "register_operand" "0")
                        (match_operand:SI 2 "immediate_operand" "i"))))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOBITOP) && riscv_bitmask_ins_p (INTVAL (operands[2]), INTVAL (operands[4]), SImode)"
{
  int len;
  riscv_bitmask (~INTVAL (operands[2]), &len, SImode);
  operands[2] = GEN_INT (len-1);
  if (operands[3] == CONST0_RTX (GET_MODE (operands[3])))
  	return "p.insert\t%0,x0,%2,%4";
  else return "p.insert\t%0,%3,%2,%4";
}
[(set_attr "type" "logical")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	LOGICAL
;;
;;  ....................
;;

;; For RV64, we don't expose the SImode operations to the rtl expanders,
;; but SImode versions exist for combine.

(define_insn "<optab><mode>3"
  [(set (match_operand:X                0 "register_operand" "=r,r")
	(any_bitwise:X (match_operand:X 1 "register_operand" "%r,r")
		       (match_operand:X 2 "arith_operand"    " r,I")))]
  ""
  "<insn>\t%0,%1,%2"
  [(set_attr "type" "logical")
   (set_attr "mode" "<MODE>")])

(define_insn "*<optab>si3_internal"
  [(set (match_operand:SI                 0 "register_operand" "=r,r")
	(any_bitwise:SI (match_operand:SI 1 "register_operand" "%r,r")
			(match_operand:SI 2 "arith_operand"    " r,I")))]
  "TARGET_64BIT"
  "<insn>\t%0,%1,%2"
  [(set_attr "type" "logical")
   (set_attr "mode" "SI")])

(define_insn "one_cmpl<mode>2"
  [(set (match_operand:X        0 "register_operand" "=r")
	(not:X (match_operand:X 1 "register_operand" " r")))]
  ""
  "not\t%0,%1"
  [(set_attr "type" "logical")
   (set_attr "mode" "<MODE>")])

(define_insn "*one_cmplsi2_internal"
  [(set (match_operand:SI         0 "register_operand" "=r")
	(not:SI (match_operand:SI 1 "register_operand" " r")))]
  "TARGET_64BIT"
  "not\t%0,%1"
  [(set_attr "type" "logical")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	TRUNCATION
;;
;;  ....................

(define_insn "truncdfsf2"
  [(set (match_operand:SF     0 "register_operand" "=f")
	(float_truncate:SF
	    (match_operand:DF 1 "register_operand" " f")))]
  "TARGET_DOUBLE_FLOAT"
  "fcvt.s.d\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "SF")])

(define_insn "truncdfhf2"
  [(set (match_operand:HF 0 "register_operand" "=xf")
  (float_truncate:HF (match_operand:DF 1 "register_operand" "f")))]
  "TARGET_DOUBLE_FLOAT && Has_F16"
  { return TARGET_MAP_DOUBLE_TO_FLOAT? "fcvt.h.s\t%0,%1": "fcvt.h.d\t%0,%1"; }
  [(set_attr "type" "fcvt")
   (set_attr "mode" "HF")])

(define_insn "truncdfohf2"
  [(set (match_operand:OHF 0 "register_operand" "=xf")
  (float_truncate:OHF (match_operand:DF 1 "register_operand" "f")))]
  "TARGET_DOUBLE_FLOAT && Has_F16ALT"
  { return TARGET_MAP_DOUBLE_TO_FLOAT? "fcvt.ah.s\t%0,%1": "fcvt.ah.d\t%0,%1"; }
  [(set_attr "type" "fcvt")
   (set_attr "mode" "OHF")])

(define_insn "truncsfhf2"
  [(set (match_operand:HF 0 "register_operand" "=xf")
  (float_truncate:HF (match_operand:SF 1 "register_operand" "f")))]
  "TARGET_HARD_FLOAT && Has_F16"
  "fcvt.h.s\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "HF")])

(define_insn "truncsfohf2"
  [(set (match_operand:OHF 0 "register_operand" "=xf")
  (float_truncate:OHF (match_operand:SF 1 "register_operand" "f")))]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  "fcvt.ah.s\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "OHF")])

;;
;;  ....................
;;
;;	ZERO EXTENSION
;;
;;  ....................

;; Extension insns.

(define_insn_and_split "zero_extendsidi2"
  [(set (match_operand:DI     0 "register_operand"     "=r,r")
	(zero_extend:DI
	    (match_operand:SI 1 "nonimmediate_operand" " r,m")))]
  "TARGET_64BIT"
  "@
   #
   lwu\t%0,%1"
  "&& reload_completed && REG_P (operands[1])"
  [(set (match_dup 0)
	(ashift:DI (match_dup 1) (const_int 32)))
   (set (match_dup 0)
	(lshiftrt:DI (match_dup 0) (const_int 32)))]
  { operands[1] = gen_lowpart (DImode, operands[1]); }
  [(set_attr "move_type" "shift_shift,load")
   (set_attr "mode" "DI")])

(define_insn_and_split "zero_extendhi<GPR:mode>2"
  [(set (match_operand:GPR 0 "register_operand" "=r,r")
        (zero_extend:GPR (match_operand:HI 1 "nonimmediate_operand_exclude_post" "r,m")))]
  ""
  {
        switch (which_alternative) {
                case 0:
                        if ((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOSEXT) return "p.exthz\t%0,%1";
                        else return "#";
                case 1:
                        if ((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG) {
                                rtx Addr = XEXP(operands[1], 0);
                                if (GET_CODE(Addr) == PLUS && (GET_CODE(XEXP(Addr, 1)) == REG || GET_CODE(XEXP(Addr, 1)) == SUBREG))
                                        return "p.lhu\t%0,%1";
                        }
                        return "lhu\t%0,%1";
                default: return "";
        }
  }
  "&& reload_completed && REG_P (operands[1]) && !((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOSEXT)"
  [(set (match_dup 0)
        (ashift:GPR (match_dup 1) (match_dup 2)))
   (set (match_dup 0)
        (lshiftrt:GPR (match_dup 0) (match_dup 2)))]
  {
    operands[1] = gen_lowpart (<GPR:MODE>mode, operands[1]);
    operands[2] = GEN_INT(GET_MODE_BITSIZE(<GPR:MODE>mode) - 16);
  }
  [(set_attr "move_type" "shift_shift,load")
   (set_attr "mode" "<GPR:MODE>")])

(define_insn "zero_extendqi<SUPERQI:mode>2"
  [(set (match_operand:SUPERQI 0 "register_operand" "=r,r")
        (zero_extend:SUPERQI
             (match_operand:QI 1 "nonimmediate_operand_exclude_post" "r,m")))]
  ""
  {
        switch (which_alternative) {
                case 0: return "and\t%0,%1,0xff";
                case 1:
                        if ((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG) {
                                rtx Addr = XEXP(operands[1], 0);
                                if (GET_CODE(Addr) == PLUS && (GET_CODE(XEXP(Addr, 1)) == REG || GET_CODE(XEXP(Addr, 1)) == SUBREG))
                                        return "p.lbu\t%0,%1";
                        }
                        return "lbu\t%0,%1";
                default:
                        return "";
        }
  }
  [(set_attr "move_type" "andi,load")
   (set_attr "mode" "<SUPERQI:MODE>")])



;;
;;  ....................
;;
;;	SIGN EXTENSION
;;
;;  ....................

(define_insn "extendsidi2"
  [(set (match_operand:DI     0 "register_operand"     "=r,r")
	(sign_extend:DI
	    (match_operand:SI 1 "nonimmediate_operand" " r,m")))]
  "TARGET_64BIT"
  "@
   sext.w\t%0,%1
   lw\t%0,%1"
  [(set_attr "move_type" "move,load")
   (set_attr "mode" "DI")])

(define_insn_and_split "extend<SHORT_ALL:mode><SUPERQI:mode>2"
  [(set (match_operand:SUPERQI 0 "register_operand" "=r,r")
        (sign_extend:SUPERQI
             (match_operand:SHORT_ALL 1 "nonimmediate_operand_exclude_post" "r,m")))]
  ""
  {
        switch (which_alternative) {
                case 0:
                        if ((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOSEXT) return "p.ext<SHORT_ALL:size>s\t%0,%1";
                        else return "#";
                case 1:
                        if ((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG) {
                                rtx Addr = XEXP(operands[1], 0);
                                if (GET_CODE(Addr) == PLUS && (GET_CODE(XEXP(Addr, 1)) == REG || GET_CODE(XEXP(Addr, 1)) == SUBREG))
                                        return "p.l<SHORT_ALL:size>\t%0,%1";
                        }
                        return "l<SHORT_ALL:size>\t%0,%1";
                default: return "";
        }
  }
  "&& reload_completed && REG_P (operands[1]) && !((Pulp_Cpu>=PULP_V0) && !TARGET_MASK_NOSEXT)"
  [(set (match_dup 0) (ashift:SI (match_dup 1) (match_dup 2)))
   (set (match_dup 0) (ashiftrt:SI (match_dup 0) (match_dup 2)))]
{
  operands[0] = gen_lowpart (SImode, operands[0]);
  operands[1] = gen_lowpart (SImode, operands[1]);
  operands[2] = GEN_INT (GET_MODE_BITSIZE (SImode)
                         - GET_MODE_BITSIZE (<SHORT_ALL:MODE>mode));
}
  [(set_attr "move_type" "shift_shift,load")
   (set_attr "mode" "SI")])

(define_insn "extendsfdf2"
  [(set (match_operand:DF     0 "register_operand" "=f")
	(float_extend:DF
	    (match_operand:SF 1 "register_operand" " f")))]
  "TARGET_DOUBLE_FLOAT"
  { return TARGET_MAP_DOUBLE_TO_FLOAT?"":"fcvt.d.s\t%0,%1"; }
  [(set_attr "type" "fcvt")
   (set_attr "mode" "DF")])

(define_insn "extendhfsf2"
  [(set (match_operand:SF 0 "register_operand" "=f")
  (float_extend:SF (match_operand:HF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16"
  "fcvt.s.h\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "SF")])

(define_insn "extendohfsf2"
  [(set (match_operand:SF 0 "register_operand" "=f")
  (float_extend:SF (match_operand:OHF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  "fcvt.s.ah\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "SF")])

(define_insn "extendhfohf2"
  [(set (match_operand:OHF 0 "register_operand" "=xf")
  (float:OHF (match_operand:HF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16 && Has_F16ALT"
  "fcvt.ah.h\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "OHF")])

(define_insn "extendohfhf2"
  [(set (match_operand:HF 0 "register_operand" "=xf")
  (float:HF (match_operand:OHF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16 && Has_F16ALT"
  "fcvt.h.ah\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "HF")])

;;
;;  ....................
;;
;;	CONVERSIONS
;;
;;  ....................

(define_insn "fix_trunc<ANYFULLF:mode><GPR:mode>2"
  [(set (match_operand:GPR      0 "register_operand" "=r")
	(fix:GPR
	    (match_operand:ANYFULLF 1 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  "fcvt.<GPR:ifmt>.<ANYFULLF:fmt> %0,%1,rtz"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<ANYFULLF:MODE>")])

(define_insn "fixuns_trunc<ANYFULLF:mode><GPR:mode>2"
  [(set (match_operand:GPR      0 "register_operand" "=r")
	(unsigned_fix:GPR
	    (match_operand:ANYFULLF 1 "register_operand" " f")))]
  "TARGET_HARD_FLOAT"
  "fcvt.<GPR:ifmt>u.<ANYFULLF:fmt> %0,%1,rtz"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<ANYFULLF:MODE>")])

(define_insn "float<GPR:mode><STDF:mode>2"
  [(set (match_operand:STDF    0 "register_operand" "= f")
	(float:STDF
	    (match_operand:GPR 1 "reg_or_0_operand" " rJ")))]
  "TARGET_HARD_FLOAT"
  "fcvt.<STDF:fmt>.<GPR:ifmt>\t%0,%z1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<STDF:MODE>")])

(define_insn "floatuns<GPR:mode><STDF:mode>2"
  [(set (match_operand:STDF    0 "register_operand" "= f")
	(unsigned_float:STDF
	    (match_operand:GPR 1 "reg_or_0_operand" " rJ")))]
  "TARGET_HARD_FLOAT"
  "fcvt.<STDF:fmt>.<GPR:ifmt>u\t%0,%z1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<STDF:MODE>")])

(define_insn "l<rint_pattern><ANYF:mode><GPR:mode>2"
  [(set (match_operand:GPR       0 "register_operand" "=r")
	(unspec:GPR
	    [(match_operand:ANYF 1 "register_operand" " f")]
	    RINT))]
  "TARGET_HARD_FLOAT"
  "fcvt.<GPR:ifmt>.<ANYF:fmt> %0,%1,<rint_rm>"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<ANYF:MODE>")])


;;
;; Use straight mapping, we assume rounding is whatever comes from fcsr, for f16_alt this is acceptable
;;
(define_insn "fix_truncohf<GPR:mode>2"
  [(set (match_operand:GPR 0 "register_operand" "=r")
        (fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16ALT"
   "fcvt.<GPR:ifmt>.ah\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "OHF")]
)

(define_insn "fix_trunchf<GPR:mode>2"
  [(set (match_operand:GPR 0 "register_operand" "=r")
        (fix:GPR (match_operand:HF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16"
   "fcvt.<GPR:ifmt>.h\t%0,%1,rtz"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "HF")]
)

;; (define_insn "fix_truncohf<GPR:mode>2_internal"
;;    [(set (match_operand:GPR 0 "register_operand" "=r")
;;          (fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
;;    "TARGET_HARD_FLOAT && Has_F16ALT"
;;    "fcvt.<GPR:ifmt>.ah\t%0,%1"
;;   [(set_attr "type" "fcvt")
;;    (set_attr "mode" "OHF")]
;; )

;; (define_expand "fix_truncohf<GPR:mode>2"
;;   [(set (match_operand:GPR 0 "register_operand" "=r")
;;         (fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
;;   "TARGET_HARD_FLOAT && Has_F16ALT"
;;   {
;;     rtx RegMODE = gen_reg_rtx (<GPR:MODE>mode);
;;     rtx RegOLD = gen_reg_rtx (<GPR:MODE>mode);
;;     emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(<GPR:MODE>mode, 0x0001)));
;;     emit_insn(gen_read_fcsr(RegOLD));
;;     emit_insn(gen_write_fcsr(RegMODE));
;;     emit_insn(gen_fix_truncohf<GPR:mode>2_internal(operands[0], operands[1]));
;;     emit_insn(gen_write_fcsr(RegOLD));
;;     DONE;
;;   }
;; )


;;
;; Use straight mapping, we assume rounding is whatever comes from fcsr, for f16_alt this is acceptable
;;
(define_insn "fixuns_truncohf<GPR:mode>2"
 [(set (match_operand:GPR 0 "register_operand" "=r")
       (unsigned_fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
 "TARGET_HARD_FLOAT && Has_F16ALT"
  "fcvt.<GPR:ifmt>u.ah\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "OHF")]
)

(define_insn "fixuns_trunchf<GPR:mode>2"
 [(set (match_operand:GPR 0 "register_operand" "=r")
       (unsigned_fix:GPR (match_operand:HF 1 "register_operand" "xf")))]
 "TARGET_HARD_FLOAT && Has_F16"
  "fcvt.<GPR:ifmt>u.h\t%0,%1,rtz"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "HF")]
)

;; (define_insn "fixuns_truncohf<GPR:mode>2_internal"
;;   [(set (match_operand:GPR 0 "register_operand" "=r")
;;         (unsigned_fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
;;   "TARGET_HARD_FLOAT && Has_F16ALT"
;;   "fcvt.<GPR:ifmt>u.ah\t%0,%1"
;;   [(set_attr "type" "fcvt")
;;    (set_attr "mode" "OHF")]
;; )

;; (define_expand "fixuns_truncohf<GPR:mode>2"
;;  [(set (match_operand:GPR 0 "register_operand" "=r")
;;        (unsigned_fix:GPR (match_operand:OHF 1 "register_operand" "xf")))]
;;  "TARGET_HARD_FLOAT && Has_F16ALT"
;;  {
;;    rtx RegMODE = gen_reg_rtx (<GPR:MODE>mode);
;;    rtx RegOLD = gen_reg_rtx (<GPR:MODE>mode);
;;    emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(<GPR:MODE>mode, 0x0001)));
;;    emit_insn(gen_read_fcsr(RegOLD));
;;    emit_insn(gen_write_fcsr(RegMODE));
;;    emit_insn(gen_fixuns_truncohf<GPR:mode>2_internal(operands[0], operands[1]));
;;    emit_insn(gen_write_fcsr(RegOLD));
;;    DONE;
;;  }
;; )

(define_insn "float<GPR:mode><SMALLF:mode>2"
  [(set (match_operand:SMALLF    0 "register_operand" "= xf")
  (float:SMALLF
      (match_operand:GPR 1 "reg_or_0_operand" " rJ")))]
  "TARGET_HARD_FLOAT && ((<SMALLF:MODE>mode == HFmode && Has_F16) || (<SMALLF:MODE>mode == OHFmode && Has_F16ALT))"
  "fcvt.<SMALLF:fmt>.<GPR:ifmt>\t%0,%z1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<SMALLF:MODE>")])

(define_insn "floatuns<GPR:mode><SMALLF:mode>2"
  [(set (match_operand:SMALLF    0 "register_operand" "= xf")
  (unsigned_float:SMALLF
      (match_operand:GPR 1 "reg_or_0_operand" " rJ")))]
  "TARGET_HARD_FLOAT && ((<SMALLF:MODE>mode == HFmode && Has_F16) || (<SMALLF:MODE>mode == OHFmode && Has_F16ALT))"
  "fcvt.<SMALLF:fmt>.<GPR:ifmt>u\t%0,%z1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "<SMALLF:MODE>")])

;;
;;  ....................
;;
;;	DATA MOVEMENT
;;
;;  ....................

;; Lower-level instructions for loading an address from the GOT.
;; We could use MEMs, but an unspec gives more optimization
;; opportunities.

(define_insn "got_load<mode>"
   [(set (match_operand:P      0 "register_operand" "=r")
	 (unspec:P
	     [(match_operand:P 1 "symbolic_operand" "")]
	     UNSPEC_LOAD_GOT))]
  ""
  "la\t%0,%1"
   [(set_attr "got" "load")
    (set_attr "mode" "<MODE>")])

(define_insn "tls_add_tp_le<mode>"
  [(set (match_operand:P      0 "register_operand" "=r")
	(unspec:P
	    [(match_operand:P 1 "register_operand" "r")
	     (match_operand:P 2 "register_operand" "r")
	     (match_operand:P 3 "symbolic_operand" "")]
	    UNSPEC_TLS_LE))]
  ""
  "add\t%0,%1,%2,%%tprel_add(%3)"
  [(set_attr "type" "arith")
   (set_attr "mode" "<MODE>")])

(define_insn "got_load_tls_gd<mode>"
  [(set (match_operand:P      0 "register_operand" "=r")
	(unspec:P
	    [(match_operand:P 1 "symbolic_operand" "")]
	    UNSPEC_TLS_GD))]
  ""
  "la.tls.gd\t%0,%1"
  [(set_attr "got" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "got_load_tls_ie<mode>"
  [(set (match_operand:P      0 "register_operand" "=r")
	(unspec:P
	    [(match_operand:P 1 "symbolic_operand" "")]
	    UNSPEC_TLS_IE))]
  ""
  "la.tls.ie\t%0,%1"
  [(set_attr "got" "load")
   (set_attr "mode" "<MODE>")])

(define_insn "auipc<mode>"
  [(set (match_operand:P           0 "register_operand" "=r")
	(unspec:P
	    [(match_operand:P      1 "symbolic_operand" "")
		  (match_operand:P 2 "const_int_operand")
		  (pc)]
	    UNSPEC_AUIPC))]
  ""
  ".LA%2: auipc\t%0,%h1"
  [(set_attr "type" "arith")
   (set_attr "cannot_copy" "yes")])

;; Instructions for adding the low 12 bits of an address to a register.
;; Operand 2 is the address: riscv_print_operand works out which relocation
;; should be applied.

(define_insn "*low<mode>"
  [(set (match_operand:P           0 "register_operand" "=r")
	(lo_sum:P (match_operand:P 1 "register_operand" " r")
		  (match_operand:P 2 "symbolic_operand" "")))]
  ""
  "addi\t%0,%1,%R2"
  [(set_attr "type" "arith")
   (set_attr "mode" "<MODE>")])

;; Allow combine to split complex const_int load sequences, using operand 2
;; to store the intermediate results.  See move_operand for details.
(define_split
  [(set (match_operand:GPR 0 "register_operand")
	(match_operand:GPR 1 "splittable_const_int_operand"))
   (clobber (match_operand:GPR 2 "register_operand"))]
  ""
  [(const_int 0)]
{
  riscv_move_integer (operands[2], operands[0], INTVAL (operands[1]));
  DONE;
})

;; Likewise, for symbolic operands.
(define_split
  [(set (match_operand:P 0 "register_operand")
	(match_operand:P 1))
   (clobber (match_operand:P 2 "register_operand"))]
  "riscv_split_symbol (operands[2], operands[1], MAX_MACHINE_MODE, NULL)"
  [(set (match_dup 0) (match_dup 3))]
{
  riscv_split_symbol (operands[2], operands[1],
		     MAX_MACHINE_MODE, &operands[3]);
})

;; 64-bit integer moves

(define_expand "movdi"
  [(set (match_operand:DI 0 "")
	(match_operand:DI 1 ""))]
  ""
{
  if (riscv_legitimize_move (DImode, operands[0], operands[1]))
    DONE;
})

(define_insn "*movdi_32bit"
  [(set (match_operand:DI 0 "nonimmediate_operand" "=r,r,r,m,  *f,*f,*r,*f,*m")
	(match_operand:DI 1 "move_operand"         " r,i,m,r,*J*r,*m,*f,*f,*f"))]
  "!TARGET_64BIT
   && (register_operand (operands[0], DImode)
       || reg_or_0_operand (operands[1], DImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,fpload,mfc,fmove,fpstore")
   (set_attr "mode" "DI")])

(define_insn "*movdi_64bit"
  [(set (match_operand:DI 0 "nonimmediate_operand" "=r,r,r, m,  *f,*f,*r,*f,*m")
	(match_operand:DI 1 "move_operand"         " r,T,m,rJ,*r*J,*m,*f,*f,*f"))]
  "TARGET_64BIT
   && (register_operand (operands[0], DImode)
       || reg_or_0_operand (operands[1], DImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,fpload,mfc,fmove,fpstore")
   (set_attr "mode" "DI")])

;; Reg - Reg load and store

(define_insn "load<mode>_ind_reg_reg"
  [(set (match_operand:SUBDISF 0 "register_operand" "=r")
        (mem:SUBDISF (plus:SI (match_operand:SI 1 "register_operand" "r")
                              (match_operand:SI 2 "register_operand" "r")))
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG)"
  "p.l<size_load_store>\t%0,%2(%1)\t# load reg(reg)"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "load<mode>_<u>ext_ind_reg_reg"
  [(set (match_operand:SUBDISF 0 "register_operand" "=r")
        (mem:SUBDISF (any_extend: SI (plus:SI (match_operand:SI 1 "register_operand" "r")
                                     (match_operand:SI 2 "register_operand" "r"))))
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG)"
  "p.l<size_load_store><u>\t%0,%2(%1)\t# load reg(reg), ext"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "store<mode>_ind_reg_reg"
  [(set (mem:SUBDISF (plus:SI (match_operand:SI 0 "register_operand" "r,r")
                              (match_operand:SI 1 "register_operand" "r,r")))
        (match_operand:SUBDISF 2 "nonmemory_operand" "r,J")
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOINDREGREG)"
  "@
   p.s<size_load_store>\t%2,%1(%0)\t# store reg(reg)
   p.s<size_load_store>\tx0,%1(%0)\t# store 0 reg(reg)"
  [(set_attr "type" "store,store")
   (set_attr "mode" "<LDSTINDMODE>")]
)

;; Event Unit Read Indirect

(define_insn "load_evt_unit"
  [(set (match_operand:SI 0 "register_operand" "=&r,r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "nonmemory_operand" "r,i")] UNSPECV_READ_EVU)
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_SLIM)"
  "@
   p.elw \t%0,%2(%1)\t# Load from Event Unit
   p.elw \t%0,%2(%1)\t# Load from Event Unit"
  [(set_attr "type" "load,load")
   (set_attr "mode" "SI,SI")]
)

;; Read/Write special purpose registers

(define_insn "read_spr"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec:SI [(match_operand:SI 1 "immediate_operand" "L")] UNSPEC_SPR_READ)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "csrrs \t%0,%1,x0\t# SPR read"
  [(set_attr "type" "load")
   (set_attr "mode" "SI")]
)

(define_insn "read_spr_vol"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec_volatile:SI [(match_operand:SI 1 "immediate_operand" "L")] UNSPECV_SPR_READ_VOL)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "csrrs \t%0,%1,x0\t# SPR read, volatile"
  [(set_attr "type" "load")
   (set_attr "mode" "SI")]
)

(define_insn "write_spr"
  [(unspec_volatile [(match_operand:SI 0 "immediate_operand" "L,L") (match_operand:SI 1 "nonmemory_operand" "r,K")] UNSPEC_SPR_WRITE)
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
 "@
  csrrw \tx0,%0,%1\t# SPR write
  csrrwi \tx0,%0,%1\t# SPR write uimm5"
)

(define_insn "read_then_write_spr"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(unspec_volatile [(match_operand:SI 1 "immediate_operand" "L,L") (match_operand:SI 2 "nonmemory_operand" "r,K")] UNSPEC_SPR_WRITE)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
 "@
  csrrw \t%0,%1,%2\t# SPR read then write
  csrrwi \t%0,%1,%2\t# SPR read then write uimm5"
)

(define_insn "spr_bit_set"
  [(unspec_volatile [(match_operand:SI 0 "immediate_operand" "L,L") (match_operand:SI 1 "nonmemory_operand" "r,K")] UNSPEC_SPR_BIT_SET)
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "@
  csrrs \tx0,%0,%1\t# SPR bit set
  csrrsi \tx0,%0,%1\t# SPR bit set uimm5"
)

(define_insn "read_then_spr_bit_set"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(unspec_volatile [(match_operand:SI 1 "immediate_operand" "L,L") (match_operand:SI 2 "nonmemory_operand" "r,K")] UNSPEC_SPR_BIT_SET)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "@
  csrrs \t%0,%1,%2\t# Read then SPR bit set
  csrrsi \t%0,%1,%2\t# Read then SPR bit set uimm5"
)

(define_insn "spr_bit_clr"
  [(unspec_volatile [(match_operand:SI 0 "immediate_operand" "L,L") (match_operand:SI 1 "nonmemory_operand" "r,K")] UNSPEC_SPR_BIT_CLR)
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "@
  csrrc \tx0,%0,%1\t# SPR bit clr
  csrrci \tx0,%0,%1\t# SPR bit clr uimm5"
)

(define_insn "read_then_spr_bit_clr"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(unspec_volatile [(match_operand:SI 1 "immediate_operand" "L,L") (match_operand:SI 2 "nonmemory_operand" "r,K")] UNSPEC_SPR_BIT_CLR)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM))"
  "@
  csrrc \t%0,%1,%2\t# Read then SPR bit clr
  csrrci \t%0,%1,%2\t# Read then SPR bit clr uimm5"
)

(define_insn "read_fcsr"
  [(set (match_operand:SI 0 "register_operand" "=r") (unspec:SI [(const_int 0)]  UNSPEC_FCSR_READ))]
  "TARGET_HARD_FLOAT"
  "frcsr\t%0"
  [(set_attr "type" "load")
   (set_attr "mode" "SI")]
)

(define_insn "write_fcsr"
  [(unspec_volatile [(match_operand:SI 0 "register_operand" "r")] UNSPEC_FCSR_WRITE)]
 "TARGET_HARD_FLOAT"
  "fscsr\t%0"
  [(set_attr "type" "store")
   (set_attr "mode" "SI")]
)


;; Open MP support

(define_expand "pulp_omp_barrier"
  [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_BARRIER)]
  "(Pulp_Cpu>=PULP_V2)"
{
	rtx Reg1 = gen_reg_rtx (SImode);
	rtx Reg2 = gen_reg_rtx (SImode);
	emit_insn(gen_movsi(Reg1, gen_rtx_CONST_INT(SImode, 0x00204000)));
	emit_insn(gen_load_evt_unit(Reg2, Reg1, gen_rtx_CONST_INT(SImode, 0x21c)));
	DONE;
}
)


;;(define_insn "pulp_omp_barrier"
;;  [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_BARRIER)
;;   (clobber (match_scratch:SI 0 "=&r"))
;;  ]
;;  "(Pulp_Cpu>=PULP_V2)"
;;  "* return riscv_explicit_load_store(operands[0], NULL, 0x2017216, 1);"
;;)

(define_expand "pulp_omp_critical_start"
  [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_CRITICAL_START)]
  "(Pulp_Cpu>=PULP_V2)"
{
	rtx Reg1 = gen_reg_rtx (SImode);
	rtx Reg2 = gen_reg_rtx (SImode);
	emit_insn(gen_movsi(Reg1, gen_rtx_CONST_INT(SImode, 0x00204000)));
	emit_insn(gen_load_evt_unit(Reg2, Reg1, gen_rtx_CONST_INT(SImode, 0xc0)));
	DONE;
}
)

;; (define_insn "pulp_omp_critical_start"
;;   [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_CRITICAL_START)
;;    (clobber (match_scratch:SI 0 "=&r"))
;;   ]
;;   "(Pulp_Cpu>=PULP_V2)"
;;   "* return riscv_explicit_load_store(operands[0], gen_rtx_REG(SImode, 0), 0x2016448, 1);"
;; )

(define_insn "writesivol"
  [(unspec_volatile [(match_operand:SI 0 "register_operand" "rJ,rJ")
		     (match_operand:SI 1 "register_operand" "r,r")
		     (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_WRITESI_VOL)]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.sw \t%z0,%2(%1)\t# Write volatile
   p.sw \t%z0,%2(%1)\t# Write volatile"
  [(set_attr "type" "store,store")
   (set_attr "mode" "SI,SI")]
)

(define_insn "writesi"
  [(unspec [(match_operand:SI 0 "register_operand" "rJ,rJ")
	    (match_operand:SI 1 "register_operand" "r,r")
	    (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPEC_WRITESI)]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.sw \t%z0,%2(%1)\t# Write non volatile
   p.sw \t%z0,%2(%1)\t# Write non volatile"
  [(set_attr "type" "store,store")
   (set_attr "mode" "SI,SI")]
)

(define_insn "readsivol"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "immediate_operand" "r,i")] UNSPECV_READSI_VOL)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.lw \t%0,%2(%1)\t# Read volatile
   p.lw \t%0,%2(%1)\t# Read volatile"
  [(set_attr "type" "load,load")
   (set_attr "mode" "SI,SI")]
)

;;(define_insn "readsi"
;;  [(set (match_operand:SI 0 "register_operand" "=r,r")
;;	(mem:SI (plus:SI (match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "const_arith_operand" "r,i")))
;;   )
;;  ]
;; "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
;;  "@
;;   p.lw \t%0,%2(%1)\t# Read non volatile
;;   p.lw \t%0,%2(%1)\t# Read non volatile"
;;  [(set_attr "type" "load,load")
;;   (set_attr "mode" "SI,SI")]
;;)

(define_expand "pulp_omp_critical_end"
  [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_CRITICAL_END)]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
{
	rtx Reg1 = gen_reg_rtx (SImode);
	rtx Reg2 = gen_reg_rtx (SImode);
	emit_insn(gen_movsi(Reg1, gen_rtx_CONST_INT(SImode, 0x00204000)));
	emit_insn(gen_writesivol(Reg2, Reg1, gen_rtx_CONST_INT(SImode, 0xc0)));
	DONE;
}
)

;;(define_insn "pulp_omp_critical_end"
;;  [(unspec_volatile [(const_int 0)] UNSPECV_OMP_PULP_CRITICAL_END)
;;   (clobber (match_scratch:SI 0 "=&r"))
;;  ]
;;  "(Pulp_Cpu>=PULP_V2)"
;;  "* return riscv_explicit_load_store(operands[0], gen_rtx_REG(SImode, 0), 0x2016448, 0);"
;;)

(define_insn "OffsetedRead"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_READ)
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.lw \t%0,%2(%1)\t# Volatile Load word offseted
   p.lw \t%0,%2(%1)\t# Volatile Load word offseted"
)

(define_insn "OffsetedReadHalf"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_READ_HALF)
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.lh \t%0,%2(%1)\t# Volatile Load half word offseted
   p.lh \t%0,%2(%1)\t# Volatile Load half word offseted"
)

(define_insn "OffsetedReadByte"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r,r") (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_READ_BYTE)
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.lb \t%0,%2(%1)\t# Volatile Load byte offseted
   p.lb \t%0,%2(%1)\t# Volatile Load byte offseted"
)

(define_insn "OffsetedWrite"
  [(unspec_volatile [(match_operand:SI 0 "reg_or_0_operand" "rJ,rJ")
		     (match_operand:SI 1 "register_operand" "r,r")
		     (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_WRITE)]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.sw \t%z0,%2(%1)\t# Offseted Write volatile
   p.sw \t%z0,%2(%1)\t# Offseted Write volatile"
  [(set_attr "type" "store,store")
   (set_attr "mode" "SI,SI")]
)

(define_insn "OffsetedWriteHalf"
  [(unspec_volatile [(match_operand:SI 0 "reg_or_0_operand" "rJ,rJ")
		     (match_operand:SI 1 "register_operand" "r,r")
		     (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_WRITE_HALF)]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.sh \t%z0,%2(%1)\t# Offseted Write Half volatile
   p.sh \t%z0,%2(%1)\t# Offseted Write Half volatile"
  [(set_attr "type" "store,store")
   (set_attr "mode" "HI,HI")]
)

(define_insn "OffsetedWriteByte"
  [(unspec_volatile [(match_operand:SI 0 "reg_or_0_operand" "rJ,rJ")
		     (match_operand:SI 1 "register_operand" "r,r")
		     (match_operand:SI 2 "nonmemory_operand" "r,I")] UNSPECV_OFFSETED_WRITE_BYTE)]
 "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "@
   p.sb \t%z0,%2(%1)\t# Offseted Write Byte volatile
   p.sb \t%z0,%2(%1)\t# Offseted Write Byte volatile"
  [(set_attr "type" "store,store")
   (set_attr "mode" "QI,QI")]
)

(define_insn "OffsetedReadOMP"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (unspec_volatile:SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "immediate_operand" "i")] UNSPECV_OFFSETED_READ_OMP)
   )
  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "p.lw \t%0,%2(%1)\t# Volatile Load offseted (OMP)"
)

(define_insn "OffsetedReadNonVol"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (unspec:SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "immediate_operand" "i")] UNSPEC_READSI_NONVOL)
   )
  ]
;;  [(set (match_operand:SI 0 "register_operand" "=r")
;;	(mem:SI (plus:SI (match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "const_arith_operand" "I")))
;;   )
;;  ]
  "(Pulp_Cpu>=PULP_V2 || Pulp_Cpu==PULP_IMG)"
  "p.lw \t%0,%2(%1)\t# Non volatile Load offseted"
)

(define_expand "OffsetedReadNonVol_m1"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (unspec:SI [(match_operand:SI 1 "register_operand" "r") (match_operand:SI 2 "immediate_operand" "i")] UNSPEC_READSI_NONVOL)
   )
  ]
 "(Pulp_Cpu>=PULP_V2 || (Pulp_Cpu==PULP_SLIM) || Pulp_Cpu==PULP_IMG)"
"{
	emit_insn (gen_OffsetedReadNonVol(operands[0], operands[1], operands[2]));
	emit_insn (gen_addsi3 (operands[0], operands[0], constm1_rtx));
	DONE;
}"
)

;; Post modified load and store

(define_insn "load<mode>_ind_postinc"
  [(set (match_operand:SUBDISF 0 "register_operand" "=r")
        (mem:SUBDISF (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "p.l<size_load_store>\t%0,<size_mem>(%1!)\t# load post inc"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "load<mode>_<u>ext_ind_postinc"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (any_extend:SI
             (mem:SUBDISF (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "p.l<size_load_store><u>\t%0,<size_mem>(%1!)\t# load post inc, ext"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "load<mode>_ind_postdec"
  [(set (match_operand:SUBDISF 0 "register_operand" "=r")
        (mem:SUBDISF (post_dec:SI (match_operand:SI 1 "register_operand" "+r")))
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "p.l<size_load_store>\t%0,-<size_mem>(%1!)\t# load post dec"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "load<mode>_<u>ext_ind_postdec"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (any_extend:SI
             (mem:SUBDISF (post_dec:SI (match_operand:SI 1 "register_operand" "+r")))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "p.l<size_load_store><u>\t%0,-<size_mem>(%1!)\t# load post dec, ext"
  [(set_attr "type" "load")
   (set_attr "mode" "<LDSTINDMODE>")]
)


(define_insn "load<mode>_ind_post_mod"
  [(set (match_operand:SUBDISF 0 "register_operand" "=r,r")
        (mem:SUBDISF (post_modify:SI (match_operand:SI 1 "register_operand" "+r,r")
                                     (plus:SI (match_dup 1) (match_operand:SI 2 "nonmemory_operand" "r,I"))))
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "@
   p.l<size_load_store>\t%0,%2(%1!)\t# load post modify reg
   p.l<size_load_store>\t%0,%2(%1!)\t# load post modify imm"
  [(set_attr "type" "load,load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "load<mode>_<u>ext_ind_post_mod"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
        (any_extend:SI
                    (mem:SUBDISF (post_modify:SI (match_operand:SI 1 "register_operand" "+r,r")
                                                 (plus:SI (match_dup 1) (match_operand:SI 2 "nonmemory_operand" "r,I"))))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "@
   p.l<size_load_store><u>\t%0,%2(%1!)\t# load post modify reg, ext
   p.l<size_load_store><u>\t%0,%2(%1!)\t# load post modify imm, ext"
  [(set_attr "type" "load,load")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "store<mode>_ind_postinc"
  [(set (mem:SUBDISF (post_inc:SI (match_operand:SI 0 "register_operand" "+r,r")))
        (match_operand:SUBDISF 1 "nonmemory_operand" "r,J")
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "@
   p.s<size_load_store>\t%1,<size_mem>(%0!)\t# store post inc
   p.s<size_load_store>\tx0,<size_mem>(%0!)\t# store 0 post inc"
  [(set_attr "type" "store,store")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "store<mode>_ind_postdec"
  [(set (mem:SUBDISF (post_dec:SI (match_operand:SI 0 "register_operand" "+r,r")))
        (match_operand:SUBDISF 1 "nonmemory_operand" "r,J")
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "@
   p.s<size_load_store>\t%1,-<size_mem>(%0!)\t# store post dec
   p.s<size_load_store>\tx0,-<size_mem>(%0!)\t# store 0 post dec"
  [(set_attr "type" "store,store")
   (set_attr "mode" "<LDSTINDMODE>")]
)

(define_insn "store<mode>_ind_postmod"
  [(set (mem:SUBDISF (post_modify:SI (match_operand:SI 0 "register_operand" "+r,r,r,r")
                                     (plus:SI (match_dup 0) (match_operand:SI 2 "nonmemory_operand" "r,r,I,I"))))
        (match_operand:SUBDISF 1 "nonmemory_operand" "r,J,r,J")
   )
  ]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOPOSTMOD)"
  "@
   p.s<size_load_store>\t%1,%2(%0!)\t# store post modify reg
   p.s<size_load_store>\tx0,%2(%0!)\t# store 0 post modify reg
   p.s<size_load_store>\t%1,%2(%0!)\t# store post modify imm
   p.s<size_load_store>\tx0,%2(%0!)\t# store 0 post modify imm"
  [(set_attr "type" "store,store,store,store")
   (set_attr "mode" "<LDSTINDMODE>")]
)

;; 32-bit Integer moves

(define_expand "mov<mode>"
  [(set (match_operand:MOVE32 0 "")
	(match_operand:MOVE32 1 ""))]
  ""
{
  if (riscv_legitimize_move (<MODE>mode, operands[0], operands[1]))
    DONE;
})

(define_insn "*mov<mode>_internal"
  [(set (match_operand:MOVE32 0 "nonimmediate_operand" "=r,r,r,r,m,YU,*f,*f,*r,*m")
        (match_operand:MOVE32 1 "move_operand" "r,T,m,YU,rJ,rJ,*r*J,*m,*f,*f"))]
  "(register_operand (operands[0], <MODE>mode) || reg_or_0_operand (operands[1], <MODE>mode)) &&
    !riscv_filter_pulp_operand(operands[0], !(Pulp_Cpu>=PULP_V0)) &&
    !riscv_filter_pulp_operand(operands[1], !(Pulp_Cpu>=PULP_V0))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,load,store,store,mtc,fpload,mfc,fpstore")
   (set_attr "mode" "SI")])

;; 32-bit v2hi vector moves

(define_expand "movv2hi"
  [(set (match_operand:V2HI 0 "")
        (match_operand:V2HI 1 ""))]
  ""
{
  if (riscv_legitimize_move (V2HImode, operands[0], operands[1]))
    DONE;
})

(define_insn "movv2hi_internal"
  [(set (match_operand:V2HI 0 "nonimmediate_operand" "=r,r,r,m")
        (match_operand:V2HI 1 "move_operand" "r,T,m,rJ"))]
  "(register_operand (operands[0], V2HImode) || reg_or_0_operand (operands[1], V2HImode)) &&
    !riscv_filter_pulp_operand(operands[0], !(Pulp_Cpu>=PULP_V0)) &&
    !riscv_filter_pulp_operand(operands[1], !(Pulp_Cpu>=PULP_V0))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store")
   (set_attr "mode" "V2HI")])

;; 32-bit v4qi vector moves

(define_expand "movv4qi"
  [(set (match_operand:V4QI 0 "")
        (match_operand:V4QI 1 ""))]
  ""
{
  if (riscv_legitimize_move (V4QImode, operands[0], operands[1]))
    DONE;
})

(define_insn "movv4qi_internal"
  [(set (match_operand:V4QI 0 "nonimmediate_operand" "=r,r,r,m")
        (match_operand:V4QI 1 "move_operand" "r,T,m,rJ"))]
  "(register_operand (operands[0], V4QImode) || reg_or_0_operand (operands[1], V4QImode)) &&
    !riscv_filter_pulp_operand(operands[0], !(Pulp_Cpu>=PULP_V0)) &&
    !riscv_filter_pulp_operand(operands[1], !(Pulp_Cpu>=PULP_V0))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store")
   (set_attr "mode" "V4QI")])

(define_expand "movmisalign<mode>"
 [(set (match_operand:MODE_PULP 0 "nonimmediate_operand" "")
       (match_operand:MODE_PULP 1 "general_operand" ""))]
 ""
{
  emit_move_insn (operands[0], operands[1]);
  DONE;
})

;; 16-bit Integer moves

;; Unlike most other insns, the move insns can't be split with
;; different predicates, because register spilling and other parts of
;; the compiler, have memoized the insn number already.
;; Unsigned loads are used because LOAD_EXTEND_OP returns ZERO_EXTEND.

(define_expand "movhi"
  [(set (match_operand:HI 0 "")
	(match_operand:HI 1 ""))]
  ""
{
  if (riscv_legitimize_move (HImode, operands[0], operands[1]))
    DONE;
})

(define_insn "*movhi_internal"
  [(set (match_operand:HI 0 "nonimmediate_operand" "=r,r,r, m,  *f,*r")
	(match_operand:HI 1 "move_operand"	   " r,T,m,rJ,*r*J,*f"))]
  "(register_operand (operands[0], HImode)
    || reg_or_0_operand (operands[1], HImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,mfc")
   (set_attr "mode" "HI")])

;; HImode constant generation; see riscv_move_integer for details.
;; si+si->hi without truncation is legal because of TRULY_NOOP_TRUNCATION.

(define_insn "*add<mode>hi3"
  [(set (match_operand:HI            0 "register_operand" "=r,r")
	(plus:HI (match_operand:HISI 1 "register_operand" " r,r")
		 (match_operand:HISI 2 "arith_operand"    " r,I")))]
  ""
  { return TARGET_64BIT ? "addw\t%0,%1,%2" : "add\t%0,%1,%2"; }
  [(set_attr "type" "arith")
   (set_attr "mode" "HI")])

(define_insn "*xor<mode>hi3"
  [(set (match_operand:HI 0 "register_operand"           "=r,r")
	(xor:HI (match_operand:HISI 1 "register_operand" " r,r")
		(match_operand:HISI 2 "arith_operand"    " r,I")))]
  ""
  "xor\t%0,%1,%2"
  [(set_attr "type" "logical")
   (set_attr "mode" "HI")])

;; 8-bit Integer moves

(define_expand "movqi"
  [(set (match_operand:QI 0 "")
	(match_operand:QI 1 ""))]
  ""
{
  if (riscv_legitimize_move (QImode, operands[0], operands[1]))
    DONE;
})

(define_insn "*movqi_internal"
  [(set (match_operand:QI 0 "nonimmediate_operand" "=r,r,r, m,  *f,*r")
	(match_operand:QI 1 "move_operand"         " r,I,m,rJ,*r*J,*f"))]
  "(register_operand (operands[0], QImode)
    || reg_or_0_operand (operands[1], QImode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,const,load,store,mtc,mfc")
   (set_attr "mode" "QI")])

;; 16-bit floating point moves

(define_expand "movhf"
  [(set (match_operand:HF 0 "")
        (match_operand:HF 1 ""))]
  ""
{
  if (riscv_legitimize_move (HFmode, operands[0], operands[1]))
    DONE;
})

(define_expand "movohf"
  [(set (match_operand:OHF 0 "")
        (match_operand:OHF 1 ""))]
  ""
{
  if (riscv_legitimize_move (OHFmode, operands[0], operands[1]))
    DONE;
})

(define_insn "*movhf_hardfloat_x"
  [(set (match_operand:HF 0 "nonimmediate_operand" "=xf,xf,xf,m,m")
        (match_operand:HF 1 "move_operand" "xf,G,m,xf,G"))]
  "Has_F16
   && (register_operand (operands[0], HFmode)
       || reg_or_0_operand (operands[1], HFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store")
   (set_attr "mode" "HF")])

(define_insn "*movohf_hardfloat_x"
  [(set (match_operand:OHF 0 "nonimmediate_operand" "=xf,xf,xf,m,m")
        (match_operand:OHF 1 "move_operand" "xf,G,m,xf,G"))]
  "Has_F16ALT
   && (register_operand (operands[0], OHFmode)
       || reg_or_0_operand (operands[1], OHFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store")
   (set_attr "mode" "OHF")])


;; 32-bit floating point moves

(define_expand "movsf"
  [(set (match_operand:SF 0 "")
	(match_operand:SF 1 ""))]
  ""
{
  if (riscv_legitimize_move (SFmode, operands[0], operands[1]))
    DONE;
})

(define_insn "*movsf_hardfloat"
  [(set (match_operand:SF 0 "nonimmediate_operand" "=f,f,f,m,m,*f,*r,  *r,*r,*m")
	(match_operand:SF 1 "move_operand"         " f,G,m,f,G,*r,*f,*G*r,*m,*r"))]
  "TARGET_HARD_FLOAT
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "mode" "SF")])

(define_insn "*movsf_softfloat"
  [(set (match_operand:SF 0 "nonimmediate_operand" "=r,r,m")
        (match_operand:SF 1 "move_operand" "Gr,m,r"))]
  "!TARGET_HARD_FLOAT
   && (register_operand (operands[0], SFmode)
       || reg_or_0_operand (operands[1], SFmode)) &&
   !((GET_CODE(operands[0]) == MEM)  && XEXP(operands[0], 0) &&
       (GET_CODE(XEXP(operands[0], 0)) == POST_INC ||
        GET_CODE(XEXP(operands[0], 0)) == POST_DEC ||
        GET_CODE(XEXP(operands[0], 0)) == POST_MODIFY)) &&
   !((GET_CODE(operands[1]) == MEM)  && XEXP(operands[1], 0) &&
       (GET_CODE(XEXP(operands[1], 0)) == POST_INC ||
        GET_CODE(XEXP(operands[1], 0)) == POST_DEC ||
        GET_CODE(XEXP(operands[1], 0)) == POST_MODIFY))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,load,store")
   (set_attr "mode" "SF")])

;; 64-bit floating point moves

(define_expand "movdf"
  [(set (match_operand:DF 0 "")
	(match_operand:DF 1 ""))]
  ""
{
  if (riscv_legitimize_move (DFmode, operands[0], operands[1]))
    DONE;
})

;; In RV32, we lack fmv.x.d and fmv.d.x.  Go through memory instead.
;; (However, we can still use fcvt.d.w to zero a floating-point register.)
(define_insn "*movdf_hardfloat_rv32"
  [(set (match_operand:DF 0 "nonimmediate_operand" "=f,f,f,m,m,  *r,*r,*m")
	(match_operand:DF 1 "move_operand"         " f,G,m,f,G,*r*G,*m,*r"))]
  "!TARGET_64BIT && TARGET_DOUBLE_FLOAT
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store,move,load,store")
   (set_attr "mode" "DF")])

(define_insn "*movdf_hardfloat_rv64"
  [(set (match_operand:DF 0 "nonimmediate_operand" "=f,f,f,m,m,*f,*r,  *r,*r,*m")
	(match_operand:DF 1 "move_operand"         " f,G,m,f,G,*r,*f,*r*G,*m,*r"))]
  "TARGET_64BIT && TARGET_DOUBLE_FLOAT
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "mode" "DF")])

(define_insn "*movdf_softfloat"
  [(set (match_operand:DF 0 "nonimmediate_operand" "= r,r, m")
	(match_operand:DF 1 "move_operand"         " rG,m,rG"))]
  "!TARGET_DOUBLE_FLOAT
   && (register_operand (operands[0], DFmode)
       || reg_or_0_operand (operands[1], DFmode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "move,load,store")
   (set_attr "mode" "DF")])

(define_split
  [(set (match_operand:MOVE64 0 "nonimmediate_operand")
	(match_operand:MOVE64 1 "move_operand"))]
  "reload_completed
   && riscv_split_64bit_move_p (operands[0], operands[1])"
  [(const_int 0)]
{
  riscv_split_doubleword_move (operands[0], operands[1]);
  DONE;
})

;; Expand in-line code to clear the instruction cache between operand[0] and
;; operand[1].
(define_expand "clear_cache"
  [(match_operand 0 "pmode_register_operand")
   (match_operand 1 "pmode_register_operand")]
  ""
{
  emit_insn (gen_fence_i ());
  DONE;
})

(define_insn "fence"
  [(unspec_volatile [(const_int 0)] UNSPECV_FENCE)]
  ""
  {
    return ((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9)?"":"%|fence%-");
  }
)

(define_insn "fence_i"
  [(unspec_volatile [(const_int 0)] UNSPECV_FENCE_I)]
  ""
  {
    return ((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9)?"": "fence.i");
  }
)

(define_expand "movmemsi"
  [(parallel [(set (match_operand:BLK 0 "general_operand")
                   (match_operand:BLK 1 "general_operand"))
              (use (match_operand:SI 2 ""))
              (use (match_operand:SI 3 "const_int_operand"))])]
  "!TARGET_MEMCPY"
{
  if (riscv_expand_block_move (operands[0], operands[1], operands[2]))
    DONE;
  else
    FAIL;
})

;;
;;  ....................
;;
;;	SHIFTS
;;
;;  ....................

(define_insn "<optab>si3"
  [(set (match_operand:SI     0 "register_operand" "= r")
	(any_shift:SI
	    (match_operand:SI 1 "register_operand" "  r")
	    (match_operand:SI 2 "arith_operand"    " rI")))]
  ""
{
  if (GET_CODE (operands[2]) == CONST_INT)
    operands[2] = GEN_INT (INTVAL (operands[2])
			   & (GET_MODE_BITSIZE (SImode) - 1));

  return TARGET_64BIT ? "<insn>w\t%0,%1,%2" : "<insn>\t%0,%1,%2";
}
  [(set_attr "type" "shift")
   (set_attr "mode" "SI")])

(define_insn "<optab>di3"
  [(set (match_operand:DI 0 "register_operand"     "= r")
	(any_shift:DI
	    (match_operand:DI 1 "register_operand" "  r")
	    (match_operand:DI 2 "arith_operand"    " rI")))]
  "TARGET_64BIT"
{
  if (GET_CODE (operands[2]) == CONST_INT)
    operands[2] = GEN_INT (INTVAL (operands[2])
			   & (GET_MODE_BITSIZE (DImode) - 1));

  return "<insn>\t%0,%1,%2";
}
  [(set_attr "type" "shift")
   (set_attr "mode" "DI")])

(define_insn "*<optab>si3_extend"
  [(set (match_operand:DI                   0 "register_operand" "= r")
	(sign_extend:DI
	    (any_shift:SI (match_operand:SI 1 "register_operand" "  r")
			  (match_operand:SI 2 "arith_operand"    " rI"))))]
  "TARGET_64BIT"
{
  if (GET_CODE (operands[2]) == CONST_INT)
    operands[2] = GEN_INT (INTVAL (operands[2]) & 0x1f);

  return "<insn>w\t%0,%1,%2";
}
  [(set_attr "type" "shift")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	VECTOR OPERATIONS
;;
;;  ....................

(define_mode_iterator VMODEINT          [V2HI V4QI])
(define_mode_iterator VMODEFLOAT        [(V2HF "Has_F16") (V2OHF "Has_F16ALT")])

(define_mode_iterator VMODEINT2         [V2HI])
(define_mode_iterator VMODEINT4         [V4QI])
(define_mode_iterator VMODEFLOAT2       [(V2HF "Has_F16") (V2OHF "Has_F16ALT")])

(define_mode_iterator VMODEALL          [(V2HF "Has_F16") (V2OHF "Has_F16ALT") V2HI V4QI])
(define_mode_iterator VMODEALL4         [V4QI])
(define_mode_iterator VMODEALL2         [(V2HF "Has_F16") (V2OHF "Has_F16ALT")  V2HI])

(define_mode_attr VINT                  [(V2HI "V2HI") (V4QI "V4QI")])
(define_mode_attr vec_type              [(V2HF "v2hf") (V2OHF "v2ohf") (V2HI "v2hi") (V4QI "v4qi")])
(define_mode_attr vec_size              [(V2HF "h") (V2OHF "h") (V2HI "h") (V4QI "b")])
(define_mode_attr float_vec_size        [(V2HF "h") (V2OHF "ah") (V2HI "h") (V4QI "b")])
(define_mode_attr int_vec_size          [(V2HF "h") (V2OHF "h") (V2HI "h") (V4QI "b")])
(define_mode_attr int_vec_type          [(V2HF "v2hi") (V2OHF "v2hi") (V2HI "v2hi") (V4QI "v4qi")])
(define_mode_attr int_vec_mode          [(V2HF "V2HI") (V2OHF "V2HI") (V2HI "V2HI") (V4QI "V4QI")])


(define_mode_attr vec_scalar            [(V2HF "SF") (V2OHF "SF") (V2HI "SI")  (V4QI "SI")])
(define_mode_attr vec_scalar_int        [(V2HI "SI") (V4QI "SI")])
(define_mode_attr vec_scalar_elmt       [(V2HF "HF") (V2OHF "OHF") (V2HI "HI")  (V4QI "QI")])

;; Vector Init

(define_insn "vec_init<VMODEINT:mode>_internal"
 [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
       (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "r,vIsdc"))
  )
 ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.add.sc.<vec_size>\t%0,x0,%1 # Vector insert Scalar Reg
  pv.add.sci.<vec_size>\t%0,x0,%W1 # Vector insert Scalar Imm"

[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_init<VMODEFLOAT:mode>_internal_x"
 [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf,xf")
       (vec_duplicate:VMODEFLOAT (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "xf,vIsdc"))
  )
 ]
"(Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT && TARGET_FPREGS_ON_GRREGS"
"@
  pv.add.sc.<int_vec_size>\t%0,x0,%1 # Vector insert Scalar Reg
  pv.add.sci.<int_vec_size>\t%0,x0,%W1 # Vector insert Scalar Imm"
[(set_attr "type" "move,move")
 (set_attr "mode" "SF,SF")]
)

(define_expand "vec_init<VMODEFLOAT:mode>_internal_f"
 [(set (match_operand:VMODEFLOAT 0 "register_operand" "")
       (vec_duplicate:VMODEFLOAT (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" ""))
  )
 ]
"(Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT && TARGET_FPREGS_ON_GRREGS"
{
  rtx Vect_Zero[4] = {const0_rtx, const0_rtx, const0_rtx, const0_rtx};
  rtx zero_vect = gen_rtx_CONST_VECTOR (<MODE>mode, gen_rtvec_v (GET_MODE_NUNITS(<MODE>mode), Vect_Zero));
  emit_insn(gen_mov<mode>_internal(operands[0], zero_vect));
  if ((GET_CODE (operands[1]) == CONST_DOUBLE) && (operands[1] != CONST0_RTX (GET_MODE (operands[1]))))
    emit_insn (gen_addsc<mode>3 (operands[0], operands[0], operands[1]));
  DONE;
}
)

(define_expand "vec_init<VMODEALL:mode>"
  [(match_operand:VMODEALL 0 "register_operand" "")
   (match_operand 1 "" "")]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  riscv_expand_vector_init (operands[0], operands[1]);
  DONE;
}
)

;; Float vector move

(define_expand "mov<VMODEFLOAT:mode>"
  [(set (match_operand:VMODEFLOAT 0 "")
        (match_operand:VMODEFLOAT 1 ""))]
  ""
{
  if (riscv_legitimize_move (<MODE>mode, operands[0], operands[1]))
    DONE;
})

(define_expand "movv1sf"
  [(set (match_operand:V1SF 0 "")
  (match_operand:V1SF 1 ""))]
  ""
{
  if (riscv_legitimize_move (V1SFmode, operands[0], operands[1]))
    DONE;
})

(define_insn "mov<VMODEFLOAT:mode>_internal"
  [(set (match_operand:VMODEFLOAT 0 "nonimmediate_operand"    "=xf,    xf, xf, m,    m, xf, r,       *r, *r, *m")
              (match_operand:VMODEFLOAT 1 "move_operand"          " xf, vIzzz,  m,xf,vIzzz,  r, xf,*r*vIzzz, *m, *r"))]
  "TARGET_HARD_FLOAT && (register_operand (operands[0], <MODE>mode) || reg_or_0_operand (operands[1], <MODE>mode))"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "mode" "SF,SF,SF,SF,SF,SF,SF,SF,SF,SF")])

(define_insn "movv1sf_internal"
  [(set (match_operand:V1SF 0 "nonimmediate_operand" "=f,f,f,m,m,*f,*r,  *r,*r,*m")
  (match_operand:V1SF 1 "move_operand" " f,vIzzz,m,f,vIzzz,*r,*f,*r*vIzzz,*m,*r"))]
  "register_operand (operands[0], V1SFmode) || reg_or_0_operand (operands[1], V1SFmode)"
  { return riscv_output_move (operands[0], operands[1]); }
  [(set_attr "move_type" "fmove,mtc,fpload,fpstore,store,mtc,mfc,move,load,store")
   (set_attr "mode" "SF,SF,SF,SF,SF,SF,SF,SF,SF,SF")])


;; Float Vector Casts v2hf <-> v2ohf

(define_insn "extendv2hfv2ohf2"
  [(set (match_operand:V2OHF 0 "register_operand" "=xf")
  (float:V2OHF (match_operand:V2HF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16 && Has_F16ALT"
  "vfcvt.ah.h\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "V2OHF")])

(define_insn "extendv2ohfv2hf2"
  [(set (match_operand:V2HF 0 "register_operand" "=xf")
  (float:V2HF (match_operand:V2OHF 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && Has_F16 && Has_F16ALT"
  "vfcvt.h.ah\t%0,%1"
  [(set_attr "type" "fcvt")
   (set_attr "mode" "V2HF")])

;; Float vector conversions

(define_insn "float<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2_internal"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
        (float:VMODEFLOAT (match_operand:<VMODEFLOAT:int_vec_mode> 1 "register_operand" "r")))]
  "TARGET_HARD_FLOAT"
  "vfcvt.<VMODEFLOAT:float_vec_size>.<VMODEFLOAT:ifmt>\t%0,%1"
  [(set_attr "type" "fcvt")]
)

(define_expand "float<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2"
[(set (match_operand:VMODEFLOAT 0 "register_operand" "")
      (float:VMODEFLOAT (match_operand:<VMODEFLOAT:int_vec_mode> 1 "register_operand" "")))]
"TARGET_HARD_FLOAT"
 {
   rtx RegMODE = gen_reg_rtx (SImode);
   rtx RegOLD = gen_reg_rtx (SImode);
   emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(SImode, 0x0001)));
   emit_insn(gen_read_fcsr(RegOLD));
   emit_insn(gen_write_fcsr(RegMODE));
   emit_insn(gen_float<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2_internal(operands[0], operands[1]));
   emit_insn(gen_write_fcsr(RegOLD));
   DONE;
 }
)

(define_insn "floatuns<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2_internal"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
        (unsigned_float:VMODEFLOAT (match_operand:<VMODEFLOAT:int_vec_mode> 1 "register_operand" "r")))]
  "TARGET_HARD_FLOAT"
  "vfcvt.<VMODEFLOAT:float_vec_size>.<VMODEFLOAT:ifmt>u\t%0,%1"
  [(set_attr "type" "fcvt")]
 )

(define_expand "floatuns<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2"
[(set (match_operand:VMODEFLOAT 0 "register_operand" "")
      (unsigned_float:VMODEFLOAT (match_operand:<VMODEFLOAT:int_vec_mode> 1 "register_operand" "")))]
"TARGET_HARD_FLOAT"
 {
   rtx RegMODE = gen_reg_rtx (SImode);
   rtx RegOLD = gen_reg_rtx (SImode);
   emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(SImode, 0x0001)));
   emit_insn(gen_read_fcsr(RegOLD));
   emit_insn(gen_write_fcsr(RegMODE));
   emit_insn(gen_floatuns<VMODEFLOAT:int_vec_type><VMODEFLOAT:vec_type>2_internal(operands[0], operands[1]));
   emit_insn(gen_write_fcsr(RegOLD));
   DONE;
 }
)


(define_insn "fix_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2_internal"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (fix:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT"
  "vfcvt.<VMODEFLOAT:ifmt>.<VMODEFLOAT:float_vec_size>\t%0,%1"
  [(set_attr "type" "fcvt")]
 )

(define_expand "fix_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2"
 [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
       (fix:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
 "TARGET_HARD_FLOAT"
 {
   rtx RegMODE = gen_reg_rtx (SImode);
   rtx RegOLD = gen_reg_rtx (SImode);
   emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(SImode, 0x0001)));
   emit_insn(gen_read_fcsr(RegOLD));
   emit_insn(gen_write_fcsr(RegMODE));
   emit_insn(gen_fix_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2_internal(operands[0], operands[1]));
   emit_insn(gen_write_fcsr(RegOLD));
   DONE;
 }
)

(define_insn "fixuns_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2_internal"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (unsigned_fix:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT"
  "vfcvt.<VMODEFLOAT:ifmt>u.<VMODEFLOAT:float_vec_size>\t%0,%1"
  [(set_attr "type" "fcvt")]
 )

(define_expand "fixuns_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2"
 [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
       (unsigned_fix:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
 "TARGET_HARD_FLOAT"
 {
   rtx RegMODE = gen_reg_rtx (SImode);
   rtx RegOLD = gen_reg_rtx (SImode);
   emit_insn(gen_movsi(RegMODE, gen_rtx_CONST_INT(SImode, 0x0001)));
   emit_insn(gen_read_fcsr(RegOLD));
   emit_insn(gen_write_fcsr(RegMODE));
   emit_insn(gen_fixuns_trunc<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>2_internal(operands[0], operands[1]));
   emit_insn(gen_write_fcsr(RegOLD));
   DONE;
 }
)

;; Helper insn
(define_insn "lshrimm<VMODEALL:mode>"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r")
        (lshiftrt:<VMODEALL:MODE> (match_operand:<VMODEALL:MODE> 1 "register_operand" "r")
                           (match_operand:SI 2 "nonmemory_operand" "K")))]
  ""
  "srli \t%0,%1,%2"
  [(set_attr "type" "shift")
   (set_attr "length" "1")])

;; Helper insn
(define_insn "or<VMODEALL:mode>"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r")
        (ior:<VMODEALL:MODE> (match_operand:<VMODEALL:MODE> 1 "register_operand" "r")
                            (match_operand:<VMODEALL:MODE> 2 "register_operand" "r")))]
  ""
  "or \t%0,%1,%2"
  [(set_attr "type" "logical")
   (set_attr "length" "1")])

;; Float vectors cast and pack

;; 2 SF -> V2HF
(define_insn "vec_pack_trunc_v1sf"
  [(set (match_operand:V2HF 0 "register_operand" "=xf")
  (vec_concat:V2HF
    (float_truncate:HF (match_operand:V1SF 1 "register_operand" "f"))
    (float_truncate:HF (match_operand:V1SF 2 "register_operand" "f"))
  )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16"
  "vfcpka.h.s \t%0,%1,%2 \t"
[(set_attr "type" "fcvt")
 (set_attr "mode" "SF")]
)

(define_insn "vec_pack_trunc_v1sf_to_v2hf_builtin"
  [(set (match_operand:V2HF 0 "register_operand" "=xf")
  (vec_concat:V2HF
    (float_truncate:HF (match_operand:SF 1 "register_operand" "f"))
    (float_truncate:HF (match_operand:SF 2 "register_operand" "f"))
  )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16"
  "vfcpka.h.s \t%0,%1,%2 \t"
[(set_attr "type" "fcvt")
 (set_attr "mode" "SF")]
)

;; 2 SF -> V2OHF
(define_insn "vec_pack_trunc_v1sf_alt"
  [(set (match_operand:V2OHF 0 "register_operand" "=xf")
  (vec_concat:V2OHF
    (float_truncate:OHF (match_operand:V1SF 1 "register_operand" "f"))
    (float_truncate:OHF (match_operand:V1SF 2 "register_operand" "f"))
  )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  "vfcpka.ah.s \t%0,%1,%2 \t"
[(set_attr "type" "fcvt")
 (set_attr "mode" "SF")]
)

(define_insn "vec_pack_trunc_v1sf_to_v2ohf_builtin"
  [(set (match_operand:V2OHF 0 "register_operand" "=xf")
  (vec_concat:V2OHF
    (float_truncate:OHF (match_operand:SF 1 "register_operand" "f"))
    (float_truncate:OHF (match_operand:SF 2 "register_operand" "f"))
  )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  "vfcpka.ah.s \t%0,%1,%2 \t"
[(set_attr "type" "fcvt")
 (set_attr "mode" "SF")]
)


;; V2HF -> V1SF (high)
(define_expand "vec_unpacks_hi_v2hf"
  [(set (match_operand:V1SF 0 "register_operand" "=f")
        (float_extend:V1SF
            (vec_select:HF
              (match_operand:V2HF 1 "register_operand" "xf")
              (parallel [(const_int 1)])
            )
          )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16"
  {
    rtx RegTMP = gen_reg_rtx (V2HFmode);
    rtx ShiftVal = gen_reg_rtx (SImode);
    rtx Temp = gen_reg_rtx (V2HFmode);
    emit_insn(gen_rtx_SET (ShiftVal, gen_rtx_CONST_INT(SImode, 2)));
    emit_insn(gen_movv2hf_internal(Temp, operands[1]));
    emit_insn(gen_lshrimmv2hf(Temp, Temp, ShiftVal));
    emit_insn(gen_movv2hf_internal(RegTMP, Temp));
    emit_insn(gen_vec_unpacks_lo_v2hf(operands[0], RegTMP));
    DONE;
  }
)

;; V2HF -> V1SF (low)
(define_insn "vec_unpacks_lo_v2hf"
  [(set (match_operand:V1SF 0 "register_operand" "=f")
        (float_extend:V1SF
            (vec_select:HF
              (match_operand:V2HF 1 "register_operand" "xf")
              (parallel [(const_int 0)])
            )
          )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16"
  "fcvt.s.h \t%0,%1 \t"
[(set_attr "type" "move")
 (set_attr "mode" "SF")]
)

;; V2OHF -> V1SF (high)
(define_expand "vec_unpacks_hi_v2ohf"
  [(set (match_operand:V1SF 0 "register_operand" "=f")
        (float_extend:V1SF
            (vec_select:OHF
              (match_operand:V2OHF 1 "register_operand" "xf")
              (parallel [(const_int 1)])
            )
          )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  {
    rtx RegTMP = gen_reg_rtx (V2OHFmode);
    rtx RegVal = gen_reg_rtx (SImode);
    rtx Temp = gen_reg_rtx (V2OHFmode);
    emit_insn(gen_rtx_SET (RegVal, gen_rtx_CONST_INT(SImode, 2)));
    emit_insn(gen_movv2ohf_internal(Temp, operands[1]));
    emit_insn(gen_lshrimmv2ohf(Temp, Temp, RegVal));
    emit_insn(gen_movv2ohf_internal(RegTMP, Temp));
    emit_insn(gen_vec_unpacks_lo_v2ohf(operands[0], RegTMP));
    DONE;
  }
)

;; V2OHF -> V1SF (low)
(define_insn "vec_unpacks_lo_v2ohf"
  [(set (match_operand:V1SF 0 "register_operand" "=f")
        (float_extend:V1SF
            (vec_select:OHF
              (match_operand:V2OHF 1 "register_operand" "xf")
              (parallel [(const_int 0)])
            )
          )
   )
  ]
  "TARGET_HARD_FLOAT && Has_F16ALT"
  "fcvt.s.ah \t%0,%1 \t"
[(set_attr "type" "move")
 (set_attr "mode" "SF")]
)


;; Vector Packing

;; (define_expand "vec_pack_hf_hf_v2hf"
;;   [(set (match_operand:V2HF 0 "register_operand" "=f")
;;         (vec_concat:V2HF
;; 		(match_operand:HF 1 "")
;; 		(match_operand:HF 2 "")
;; 	)
;;    )
;;   ]
;;   "TARGET_HARD_FLOAT && Has_F16"
;;   {
;; 	rtx R0 = gen_reg_rtx(HFmode);
;; 	rtx R1 = gen_reg_rtx(HFmode);
;; 	emit_insn(gen_movhf(R0, operands[1]));
;; 	emit_insn(gen_movhf(R1, operands[2]));
;; 	emit_insn(gen_vec_pack_v2hf(operands[0], R0, R1));
;; 	// DONE;
;;   }
;; )

;; (define_expand "vec_pack_ohf_ohf_v2ohf"
;;   [(set (match_operand:V2OHF 0 "register_operand" "=f")
;;         (vec_concat:V2OHF
;; 		(match_operand:OHF 1 "")
;; 		(match_operand:OHF 2 "")
;; 	)
;;    )
;;   ]
;;   "TARGET_HARD_FLOAT && Has_F16ALT"
;;   {
;; 	rtx R0 = gen_reg_rtx(OHFmode);
;; 	rtx R1 = gen_reg_rtx(OHFmode);
;; 	emit_insn(gen_movhf(R0, operands[1]));
;; 	emit_insn(gen_movhf(R1, operands[2]));
;; 	emit_insn(gen_vec_pack_v2ohf(operands[0], R0, R1));
;; 	// DONE;
;;   }
;; )

(define_insn "vec_pack_<VMODEALL2:mode>"
  [(set	(match_operand:VMODEALL2 0 "register_operand" "=r")
	(vec_concat:VMODEALL2
		(match_operand:<vec_scalar_elmt> 1 "register_operand" "r")
		(match_operand:<vec_scalar_elmt> 2 "register_operand" "r")
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.pack.h \t%0,%2,%1 \t# Vector pack of 2 shorts"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

(define_insn "vec_pack_v4qi_lo"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
	(vec_merge:V4QI
		(vec_concat:V4QI
			(vec_concat:V2QI
				(match_operand:QI 1 "register_operand" "r")
				(match_operand:QI 2 "register_operand" "r")
			)
			(const_vector:V2QI [(const_int 0) (const_int 0)])
		)
          	(match_operand:V4QI 3 "register_operand" "0")
		(const_int 3)
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.packlo.b \t%0,%2,%1 \t# Vector pack of 2 bytes, low part"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

(define_insn "vec_pack_v4qi_lo_first"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
	(vec_merge:V4QI
		(vec_concat:V4QI
			(vec_concat:V2QI
				(match_operand:QI 1 "register_operand" "r")
				(match_operand:QI 2 "register_operand" "r")
			)
			(const_vector:V2QI [(const_int 0) (const_int 0)])
		)
	  	(const_vector:V4QI [(const_int 0) (const_int 0) (const_int 0) (const_int 0)])
		(const_int 3)
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.packlo.b \t%0,%2,%1 \t# Vector pack of 2 bytes (first), low part"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)


(define_insn "vec_pack_v4qi_hi"
  [(set	(match_operand:V4QI 0 "register_operand" "=r")
	(vec_merge:V4QI
		(vec_concat:V4QI
			(const_vector:V2QI [(const_int 0) (const_int 0)])
			(vec_concat:V2QI
				(match_operand:QI 1 "register_operand" "r")
				(match_operand:QI 2 "register_operand" "r")
			)
		)
          	(match_operand:V4QI 3 "register_operand" "0")
		(const_int 12)
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.packhi.b \t%0,%2,%1 \t# Vector pack of 2 bytes, high part"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

;;(define_insn "vec_pack_v4qi_hi_first"
;;  [(set	(match_operand:V4QI 0 "register_operand" "=r")
;;	(vec_merge:V4QI
;;		(vec_concat:V4QI
;;			(const_vector:V2QI [(const_int 0) (const_int 0)])
;;			(vec_concat:V2QI
;;				(match_operand:QI 1 "register_operand" "r")
;;				(match_operand:QI 2 "register_operand" "r")
;;			)
;;		)
;;	  	(const_vector:V4QI [(const_int 0) (const_int 0) (const_int 0) (const_int 0)])
;;		(const_int 12)
;;	)
;;   )
;;  ]
;;  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
;;  "pv.packhi.b \t%0,%2,%1 \t# Vector pack of 2 bytes (first), high part"
;;[(set_attr "type" "move")
;; (set_attr "mode" "SI")]
;;)


(define_expand "vec_pack_v4qi"
  [(match_operand:V4QI 0 "register_operand" "")
   (match_operand:QI 1 "register_operand" "")
   (match_operand:QI 2 "register_operand" "")
   (match_operand:QI 3 "register_operand" "")
   (match_operand:QI 4 "register_operand" "")
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
{
	rtx R0 = gen_reg_rtx(QImode);
	rtx R1 = gen_reg_rtx(QImode);
	rtx R2 = gen_reg_rtx(QImode);
	rtx R3 = gen_reg_rtx(QImode);
	emit_insn(gen_movqi(R0, operands[1]));
	emit_insn(gen_movqi(R1, operands[2]));
	emit_insn(gen_movqi(R2, operands[3]));
	emit_insn(gen_movqi(R3, operands[4]));
	emit_insn (gen_vec_pack_v4qi_lo_first(operands[0], R0, R1));
	emit_insn (gen_vec_pack_v4qi_hi      (operands[0], R2, R3, operands[0]));
/*
	emit_insn (gen_vec_pack_v4qi_lo_first(operands[0], operands[1], operands[2]));
	emit_insn (gen_vec_pack_v4qi_hi      (operands[0], operands[3], operands[4], operands[0]));
*/
  DONE;
})

;; Vector permutation

(define_insn "vec_perm<VMODEALL2:mode>_internal2_1"
  [(set (match_operand:VMODEALL2 0 "register_operand"               "=r,r")
        (unspec:VMODEALL2 [(match_operand:VMODEALL2 1 "register_operand"  "r,r")
                           (match_operand:VMODEALL2 2 "register_operand"  "1,1")
                           (match_operand:VMODEALL2 3 "permute_sel_operand" "r,i")
		          ] UNSPEC_VEC_PERM2)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK)  && riscv_valid_permute_operands (operands[1], operands[2], operands[3]))"
{
	switch (which_alternative) {
		case 0:
			return "pv.shuffle.h\t%0,%1,%3";
		case 1:
			{
				int Mask=0;
				rtx xoperands[3];
				int i;

				xoperands[0] = operands[0]; xoperands[1] = operands[2];
  				for (i = 0; i < 2; ++i) Mask |= (((INTVAL (XVECEXP (operands[3], 0, i)) & 1))<<(4*i));
				Mask = Mask & 0x0FF;
				xoperands[2] = gen_rtx_CONST_INT (SImode, Mask);
				output_asm_insn("pv.shuffle.sci.h\t%0,%1,%2", xoperands);
				return "";
			}
		default:
			return "";
	}
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_perm<VMODEALL2:mode>_internal2"
  [(set (match_operand:VMODEALL2 0 "register_operand"               "=r")
        (unspec:VMODEALL2 [(match_operand:VMODEALL2 1 "register_operand" "0")
                           (match_operand:VMODEALL2 2 "register_operand" "r")
                           (match_operand:VMODEALL2 3 "register_operand" "r")
		          ] UNSPEC_VEC_PERM3)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.shuffle2.h\t%0,%2,%3 \t# Shuffle2, word"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

(define_insn "vec_perm<VMODEALL2:mode>_int1"
  [(set (match_operand:VMODEALL2 0 "register_operand"               "=r,r")
        (unspec:VMODEALL2 [(match_operand:VMODEALL2 1 "register_operand"  "r,r")
                           (match_operand:VMODEALL2 2 "permute_sel_operand" "r,i")
		          ] UNSPEC_VEC_PERM1)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
{
	switch (which_alternative) {
		case 0:
			return "pv.shuffle.h\t%0,%1,%2";
		case 1: {
				unsigned int Mask=0;
				rtx xoperands[3];
				int i;

				xoperands[0] = operands[0]; xoperands[1] = operands[1];
  				for (i = 0; i < 2; ++i) Mask |= (((INTVAL (XVECEXP (operands[2], 0, i)) & 1))<<(4*i));
				Mask = Mask & 0x0FF;
				xoperands[2] = gen_rtx_CONST_INT (SImode, Mask);
				output_asm_insn("pv.shuffle.sci.h\t%0,%1,%2", xoperands);
				return "";
			}
		default:
			return "";
	}
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

/* __GAP8 Start */

(define_insn "vec_perm<VMODEALL2:mode>_low"
  [(set (match_operand:VMODEALL2 0 "register_operand"                  "=r,r")
        (unspec:VMODEALL2 [(match_operand:VMODEALL2 1 "register_operand"    "r,r")
                           (match_operand:VMODEALL2 2 "permute_sel_operand" "r,i")
                          ] UNSPEC_VEC_PERM4)
   )
  ]
  "((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  {
	if (Pulp_Cpu==PULP_GAP8) return "pv.pack.l.h \t%0,%2,%1 \t# Pack2 low";
	else return "pv.pack.h \t%0,%2,%1 \t# Vector pack of 2 shorts";
  }
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_perm<VMODEALL2:mode>_high"
  [(set (match_operand:VMODEALL2 0 "register_operand"                  "=r,r")
        (unspec:VMODEALL2 [(match_operand:VMODEALL2 1 "register_operand"    "r,r")
                           (match_operand:VMODEALL2 2 "permute_sel_operand" "r,i")
                          ] UNSPEC_VEC_PERM5)
   )
  ]
  "((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.pack.h.h \t%0,%2,%1 \t# Pack2 high"
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

/* __GAP8 Stop */

(define_expand "vec_perm<VMODEALL2:mode>"
  [(match_operand:VMODEALL2 0 "register_operand"    "")
   (match_operand:VMODEALL2 1 "register_operand"    "")
   (match_operand:VMODEALL2 2 "register_operand"    "")
   (match_operand:VMODEALL2 3 "permute_sel_operand" "")
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
{
	if (rtx_equal_p(operands[1], operands[2])) {
		emit_insn (gen_vec_permv2hi_internal2_1 (operands[0], operands[1], operands[2], operands[3]));
	} else {
		/* __GAP8 Start */
                if ((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && (GET_CODE (operands[3]) == CONST_VECTOR) &&
                    (INTVAL(XVECEXP (operands[3], 0, 0)) == 0) && (INTVAL(XVECEXP (operands[3], 0, 1)) == 2)) {
			emit_insn (gen_vec_permv2hi_low(operands[0], operands[1], operands[2]));
                } else if ((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && (GET_CODE (operands[3]) == CONST_VECTOR) &&
                           (INTVAL(XVECEXP (operands[3], 0, 0)) == 1) && (INTVAL(XVECEXP (operands[3], 0, 1)) == 3)) {
                        emit_insn (gen_vec_permv2hi_high(operands[0], operands[1], operands[2]));
                } else
		/* __GAP8 Stop */
		{
                        if (GET_CODE (operands[3]) != REG) operands[3] = force_reg (V2HImode, operands[3]);
                        emit_insn (gen_vec_permv2hi_internal2 (operands[0], operands[1], operands[2], operands[3]));
                }
	}
	DONE;
}
)

(define_insn "vec_permv4qi_internal2_1"
  [(set (match_operand:V4QI 0 "register_operand"               "=r,r")
        (unspec:V4QI [(match_operand:V4QI 1 "register_operand"  "r,r")
                      (match_operand:V4QI 2 "register_operand"  "1,1")
                      (match_operand:V4QI 3 "permute_sel_operand" "r,i")
		     ] UNSPEC_VEC_PERM2)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK)  && riscv_valid_permute_operands (operands[1], operands[2], operands[3]))"
{
	switch (which_alternative) {
		case 0:
			return "pv.shuffle.b\t%0,%1,%3";
		case 1:
			{
				int Mask=0;
				int Sel = INTVAL (XVECEXP (operands[3], 0, 3)) & 3;
				rtx xoperands[3];
				int i;

				xoperands[0] = operands[0]; xoperands[1] = operands[2];
  				for (i = 0; i < 3; ++i) Mask |= (((INTVAL (XVECEXP (operands[3], 0, i)) & 3))<<(2*i));
				xoperands[2] = gen_rtx_CONST_INT (SImode, Mask);
				switch (Sel) {
					case 0: output_asm_insn("pv.shuffleI0.sci.b\t%0,%1,%2", xoperands); break;
					case 1: output_asm_insn("pv.shuffleI1.sci.b\t%0,%1,%2", xoperands); break;
					case 2: output_asm_insn("pv.shuffleI2.sci.b\t%0,%1,%2", xoperands); break;
					case 3: output_asm_insn("pv.shuffleI3.sci.b\t%0,%1,%2", xoperands); break;
					default:;
				}
				return "";
			}
		default:
			return "";
	}
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_permv4qi_internal2"
  [(set (match_operand:V4QI 0 "register_operand"               "=r")
        (unspec:V4QI [(match_operand:V4QI 1 "register_operand" "0")
                      (match_operand:V4QI 2 "register_operand" "r")
                      (match_operand:V4QI 3 "register_operand" "r")
		     ] UNSPEC_VEC_PERM3)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.shuffle2.b\t%0,%2,%3 \t# Shuffle2, bytes"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

(define_insn "vec_permv4qi_int1"
  [(set (match_operand:V4QI 0 "register_operand"               "=r,r")
        (unspec:V4QI [(match_operand:V4QI 1 "register_operand"  "r,r")
                      (match_operand:V4QI 2 "permute_sel_operand" "r,i")
		     ] UNSPEC_VEC_PERM1)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
{
	switch (which_alternative) {
		case 0:
			return "pv.shuffle.b\t%0,%1,%2";
		case 1: {
				int Mask=0;
				int Sel = INTVAL (XVECEXP (operands[3], 0, 3)) & 3;
				rtx xoperands[3];
				int i;

				xoperands[0] = operands[0]; xoperands[1] = operands[1];
  				for (i = 0; i < 3; ++i) Mask |= (((INTVAL (XVECEXP (operands[2], 0, i)) & 3))<<(2*i));
				xoperands[2] = gen_rtx_CONST_INT (SImode, Mask);
				switch (Sel) {
					case 0: output_asm_insn("pv.shuffleI0.sci.b\t%0,%1,%2", xoperands); break;
					case 1: output_asm_insn("pv.shuffleI1.sci.b\t%0,%1,%2", xoperands); break;
					case 2: output_asm_insn("pv.shuffleI2.sci.b\t%0,%1,%2", xoperands); break;
					case 3: output_asm_insn("pv.shuffleI3.sci.b\t%0,%1,%2", xoperands); break;
					default:;
				}
				return "";
			}
		default:
			return "";
	}
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_expand "vec_permv4qi"
  [(match_operand:V4QI 0 "register_operand" "")
   (match_operand:V4QI 1 "register_operand" "")
   (match_operand:V4QI 2 "register_operand" "")
   (match_operand:V4QI 3 "permute_sel_operand" "")
  ]
  "((Pulp_Cpu>=PULP_V2) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
{
	if (rtx_equal_p(operands[1], operands[2])) {
		emit_insn (gen_vec_permv4qi_internal2_1 (operands[0], operands[1], operands[2], operands[3]));
	} else {
		if (GET_CODE (operands[3]) != REG) operands[3] = force_reg (V4QImode, operands[3]);
		emit_insn (gen_vec_permv4qi_internal2 (operands[0], operands[1], operands[2], operands[3]));
	}

	DONE;
}
)

;; Vector Insert

(define_insn "vec_set<VMODEALL:mode>_internal"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r,r")
        (vec_merge:VMODEALL
          (vec_duplicate:VMODEALL (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "r,J"))
          (match_operand:VMODEALL 3 "register_operand" "0,0")
          (match_operand:SI 2 "immediate_operand" "i,i")))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  int elt = ffs ((int) INTVAL (operands[2])) - 1;

  operands[2] = GEN_INT (elt);
  if (which_alternative == 0) return "pv.insert.<vec_size>\t%0,%1,%2\t # Vect insert";
  else return "pv.insert.<vec_size>\t%0,x0,%2\t # Vect insert 0";
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_set_first<VMODEALL2:mode>_internal"
  [(set (match_operand:VMODEALL2 0 "register_operand" "=r,r")
        (vec_merge:VMODEALL2
          (vec_duplicate:VMODEALL2 (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "r,J"))
	  (const_vector:VMODEALL2 [(const_int 0) (const_int 0)])
          (match_operand:SI 2 "const_1_operand" "Z,Z")))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  int elt = ffs ((int) INTVAL (operands[2])) - 1;

  operands[2] = GEN_INT (elt);
  if (which_alternative == 0) {
	return "p.exthz \t%0,%1\t # Vect first insert half, pos 0";
  } else return "add\t%0,x0,%2\t # Vect first insert half 0, pos 0";
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_insn "vec_set_first<VMODEALL4:mode>_internal"
  [(set (match_operand:VMODEALL4 0 "register_operand" "=r,r")
        (vec_merge:VMODEALL4
          (vec_duplicate:VMODEALL4 (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "r,J"))
	  (const_vector:VMODEALL4 [(const_int 0) (const_int 0) (const_int 0) (const_int 0)])
          (match_operand:SI 2 "const_1_operand" "Z,Z")))]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  int elt = ffs ((int) INTVAL (operands[2])) - 1;

  operands[2] = GEN_INT (elt);
  if (which_alternative == 0) {
	return "and\t%0,%1,0xff\t # Vect first insert byte, pos 0";
  } else return "add\t%0,x0,%2\t # Vect first insert, pos 0";
}
[(set_attr "type" "move,move")
 (set_attr "mode" "SI,SI")]
)

(define_expand "vec_set_first<VMODEALL:mode>"
  [(match_operand:VMODEALL 0 "register_operand" "")
   (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "")
   (match_operand:SI 2 "immediate_operand" "")]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  HOST_WIDE_INT elem = (HOST_WIDE_INT) 1 << INTVAL (operands[2]);	/* Should always be 1 */

  if ((GET_CODE (operands[1]) == CONST_INT) && (INTVAL(operands[1]) != 0)) {
	rtx Vect_Zero[4] = {const0_rtx, const0_rtx, const0_rtx, const0_rtx};
	rtx zero_vect = gen_rtx_CONST_VECTOR (<MODE>mode, gen_rtvec_v (GET_MODE_NUNITS(<MODE>mode), Vect_Zero));
	emit_insn(gen_mov<mode>_internal(operands[0], zero_vect));
  	emit_insn (gen_vec_set<mode>_internal (operands[0], operands[1], GEN_INT (elem), operands[0]));
  } else emit_insn (gen_vec_set_first<mode>_internal (operands[0], operands[1], GEN_INT (elem)));
  DONE;
})

(define_expand "vec_set<VMODEALL:mode>"
  [(match_operand:VMODEALL 0 "register_operand" "")
   (match_operand:<vec_scalar_elmt> 1 "nonmemory_operand" "")
   (match_operand:SI 2 "immediate_operand" "")]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
{
  HOST_WIDE_INT elem = (HOST_WIDE_INT) 1 << INTVAL (operands[2]);
  emit_insn (gen_vec_set<mode>_internal (operands[0], operands[1], GEN_INT (elem), operands[0]));
  DONE;
})

;; Vector Extract

(define_insn "vec_extract_sext_<SUBDI:mode>_<VMODEALL:mode>"
  [(set (match_operand:SUBDI 0 "register_operand" "=r")
        (sign_extend:SUBDI
          (vec_select:<vec_scalar_elmt>
             (match_operand:VMODEALL 1 "register_operand" "r")
             (parallel [(match_operand:SI 2 "immediate_operand" "i")])
          )
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "pv.extract.<vec_size>\t%0,%1,%2\t # vect extract, with sign ext"
[(set_attr "type" "move")
 (set_attr "mode" "<SUBDI:MODE>")]
)

(define_insn "vec_extract_zext_<SUBDI:mode>_<VMODEALL:mode>"
  [(set (match_operand:SUBDI 0 "register_operand" "=r")
        (zero_extend:SUBDI
          (vec_select:<vec_scalar_elmt>
             (match_operand:VMODEALL 1 "register_operand" "r")
             (parallel [(match_operand:SI 2 "immediate_operand" "i")])
          )
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "pv.extractu.<vec_size>\t%0,%1,%2\t # vect extract, with zero ext"
[(set_attr "type" "move")
 (set_attr "mode" "<SUBDI:MODE>")]
)

(define_insn "vec_extract<VMODEALL:mode>"
  [(set (match_operand:<vec_scalar_elmt> 0 "register_operand" "=r")
        (vec_select:<vec_scalar_elmt>
           (match_operand:VMODEALL 1 "register_operand" "r")
           (parallel [(match_operand:SI 2 "immediate_operand" "i")])
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "pv.extract.<vec_size>\t%0,%1,%2\t # vect extract"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

;; Diadic Instructions

(define_code_iterator vec_op2      	[plus minus smin smax])
(define_code_iterator vec_op2_float    	[plus minus smin smax mult])
(define_code_iterator vec_op2u      	[umin umax])
(define_code_iterator vec_op2s     	[lshiftrt ashiftrt ashift])
(define_code_iterator vec_log2     	[and ior xor])


(define_code_attr vec_op2_name      	[(plus "add") (minus "sub") (smin "smin") (smax "smax") (mult "mul")])
(define_code_attr vec_op2u_name      	[(umin "umin") (umax "umax")])
(define_code_attr vec_op2s_name     	[(lshiftrt "vlshr") (ashiftrt "vashr") (ashift "vashl")])
(define_code_attr vec_log2_name    	[(and "and") (ior "ior") (xor "exor")])

(define_code_attr vec_op2_asm_name 	[(plus "add") (minus "sub") (smin "min") (smax "max") (mult "mul")])
(define_code_attr vec_op2u_asm_name 	[(umin "minu") (umax "maxu")])
(define_code_attr vec_op2s_asm_name 	[(lshiftrt "srl") (ashiftrt "sra") (ashift "sll")])
(define_code_attr vec_log2_asm_name 	[(and "and") (ior "or") (xor "xor")])


/* __GAP8 Start */

(define_insn "cplx_conjhi2"
 [(set (match_operand:V2HI 0 "register_operand" "=r")
       (vec_concat:V2HI
		(vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
		(neg:HI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
       )
  )
 ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxconj.h \t%0,%1\t # Complex conjugate"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplx_conjsi3"
 [(set (match_operand:V2HI 0 "register_operand" "=r")
       (vec_concat:V2HI
		(subreg:HI (match_operand:SI 1 "register_operand" "r") 0)
		(subreg:HI (neg:SI (match_operand:SI 2 "register_operand" "r")) 0)
       )
  )
 ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxconj.h \t%0,%1\t # Complex conjugate, infered"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "add_div2_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (plus   (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 1) (const_int 1)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.add.h.div2 \t%0,%1,%2\t # Add2>>1 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "add_div2_v4qi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
        (ashiftrt:V4QI
                (plus   (match_operand:V4QI 1 "register_operand" "r")
                        (match_operand:V4QI 2 "register_operand" "r")
                )
                (const_vector:V4QI [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.add.b.div2 \t%0,%1,%2\t # Add4>>1 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "add_div4_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (plus   (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 2) (const_int 2)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.add.h.div4 \t%0,%1,%2\t # Add2>>2 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "add_div8_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (plus   (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 3) (const_int 3)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.add.h.div8 \t%0,%1,%2\t # Add2>>3 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "add_div4_v4qi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
        (ashiftrt:V4QI
                (plus   (match_operand:V4QI 1 "register_operand" "r")
                        (match_operand:V4QI 2 "register_operand" "r")
                )
                (const_vector:V4QI [(const_int 2) (const_int 2) (const_int 2) (const_int 2)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.add.b.div4 \t%0,%1,%2\t # Add4>>2 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sub_div2_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (minus  (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 1) (const_int 1)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.sub.h.div2 \t%0,%1,%2\t # Sub2>>1 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sub_div2_v4qi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
        (ashiftrt:V4QI
                (minus  (match_operand:V4QI 1 "register_operand" "r")
                        (match_operand:V4QI 2 "register_operand" "r")
                )
                (const_vector:V4QI [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.sub.b.div2 \t%0,%1,%2\t # Sub4>>1 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sub_div4_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (minus  (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 2) (const_int 2)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.sub.h.div4 \t%0,%1,%2\t # Sub2>>2 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sub_div8_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (ashiftrt:V2HI
                (minus  (match_operand:V2HI 1 "register_operand" "r")
                        (match_operand:V2HI 2 "register_operand" "r")
                )
                (const_vector:V2HI [(const_int 3) (const_int 3)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.sub.h.div8 \t%0,%1,%2\t # Sub2>>3 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sub_div4_v4qi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
        (ashiftrt:V4QI
                (minus  (match_operand:V4QI 1 "register_operand" "r")
                        (match_operand:V4QI 2 "register_operand" "r")
                )
                (const_vector:V4QI [(const_int 2) (const_int 2) (const_int 2) (const_int 2)])
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.sub.b.div4 \t%0,%1,%2\t # Sub4>>2 Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "subrotmj_v2hi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (vec_concat:V2HI
                (subreg:HI
                        (minus:SI
                                (sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r")
                                                               (parallel [(const_int 1)]))
                                )
                                (sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "register_operand" "r")
                                                               (parallel [(const_int 1)]))
                                )
                        )
                        0
                )
                (subreg:HI
                        (minus:SI
                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 0)])))
                        )
                        0
                )
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8||Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.subrotmj.h \t%0,%1,%2"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)
/* __GAP8 Stop */

(define_insn "<vec_op2_name><VMODEFLOAT:mode>3"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
        (vec_op2_float:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" "xf")
                                  (match_operand:VMODEFLOAT 2 "register_operand" "xf")
        )
   )
  ]
 "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
"vf<vec_op2_asm_name>.<float_vec_size> \t%0,%1,%2\t # FVect Op FVect"
[(set_attr "type" "fmadd")
 (set_attr "mode" "<VMODEFLOAT:MODE>")]
)

(define_insn "<vec_op2_name>sc<VMODEFLOAT:mode>3"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
        (vec_op2_float:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" "xf")
                                  (vec_duplicate:VMODEFLOAT (match_operand:<vec_scalar_elmt> 2 "register_operand" "xf"))
              )
   )]
 "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
"vf<vec_op2_asm_name>.r.<float_vec_size> \t%0,%1,%2\t # FVect Op Scalar"
[(set_attr "type" "fmadd")
 (set_attr "mode" "SF")]
)

(define_insn "<vec_op2_name><VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
        (vec_op2:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r,r")
                          (match_operand:VMODEINT 2 "nonmemory_operand" "r,vIsdc")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.<vec_op2_asm_name>.<vec_size> \t%0,%1,%2\t # Vect Op Vect
  pv.<vec_op2_asm_name>.sci.<vec_size> \t%0,%1,%W2\t # Vect Op Immediate Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "<vec_op2_name>sc<VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (vec_op2:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r")
			  (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 2 "register_operand" "r"))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2_asm_name>.sc.<vec_size> \t%0,%1,%2\t # Vect Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "<vec_op2_name>_swap_sc<VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (vec_op2:VMODEINT (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 1 "register_operand" "r"))
		          (match_operand:VMODEINT 2 "register_operand" "r")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2_asm_name>.sc.<vec_size> \t%0,%2,%1\t # Vect Op Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; op0 += op1 * op02
(define_insn "fma<VMODEFLOAT:mode>3_internal"
 [(set (match_operand:VMODEFLOAT                 0 "register_operand" "+xf")
       (fma:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" " xf")
                       (match_operand:VMODEFLOAT 2 "register_operand" " xf")
                       (match_dup                0)
        )
 )]
 "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
 "vfmac.<float_vec_size>\t%0,%1,%2"
 [(set_attr "type" "fmadd")
  (set_attr "mode" "<VMODEFLOAT:MODE>")])


;; op0 = op1 * op2 + op3
(define_expand "fma<VMODEFLOAT:mode>4"
 [(set (match_operand:VMODEFLOAT                 0 "register_operand" " ")
       (fma:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" " ")
                       (match_operand:VMODEFLOAT 2 "register_operand" " ")
                       (match_operand:VMODEFLOAT 3 "register_operand" " "))
 )]
 "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
  {
    emit_insn(gen_mov<VMODEFLOAT:mode>(operands[0], operands[3]));
    emit_insn(gen_fma<VMODEFLOAT:mode>3_internal(operands[0], operands[1], operands[2]));
    DONE;
  }
)

;; op0 = op1 * op2 - op0
;;(define_insn "fms<VMODEFLOAT:mode>3_internal"
;;  [(set (match_operand:VMODEFLOAT                 0 "register_operand" "+xf")
;;        (fma:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" " xf")
;;                        (match_operand:VMODEFLOAT 2 "register_operand" " xf")
;;                        (neg:VMODEFLOAT (match_dup 0))))]
;;  "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
;;  "vfmre.<float_vec_size>\t%0,%1,%2"
;;  [(set_attr "type" "fmadd")
;;   (set_attr "mode" "<VMODEFLOAT:MODE>")])

;; d = a * b - c
;;(define_expand "fms<VMODEFLOAT:mode>4"
;;  [(set (match_operand:VMODEFLOAT                                 0 "register_operand" " ")
;;        (fma:VMODEFLOAT (match_operand:VMODEFLOAT                 1 "register_operand" " ")
;;                        (match_operand:VMODEFLOAT                 2 "register_operand" " ")
;;                        (neg:VMODEFLOAT (match_operand:VMODEFLOAT 3 "register_operand" " "))))]
;;  "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
;;  {
;;    emit_insn(gen_mov<VMODEFLOAT:mode>(operands[0], operands[3]));
;;    emit_insn(gen_fms<VMODEFLOAT:mode>3_internal(operands[0], operands[1], operands[2]));
;;    DONE;
;;  }
;;)

(define_insn "fms<VMODEFLOAT:mode>4"
  [(set (match_operand:VMODEFLOAT                                 0 "register_operand" "=xf")
        (fma:VMODEFLOAT (match_operand:VMODEFLOAT                 1 "register_operand" " xf")
                        (match_operand:VMODEFLOAT                 2 "register_operand" " xf")
			(neg:VMODEFLOAT (match_operand:VMODEFLOAT 3 "register_operand" " 0"))))]
  "TARGET_HARD_FLOAT && (Has_F16 || Has_F16ALT)"
  "vfmre.<float_vec_size>\t%0,%1,%2"
  [(set_attr "type" "fmadd")
   (set_attr "mode" "<VMODEFLOAT:MODE>")])


;; Vector copysign */
(define_insn "copysign<VMODEFLOAT:mode>3"
  [(set (match_operand:VMODEFLOAT 0 "register_operand"               "=xf")
  (unspec:VMODEFLOAT [(match_operand:VMODEFLOAT 1 "register_operand" " xf")
          (match_operand:VMODEFLOAT 2 "register_operand" " xf")]
         UNSPEC_COPYSIGN))]
  "TARGET_HARD_FLOAT &&  (Has_F16 || Has_F16ALT)"
  "vfsgnj.<float_vec_size>\t%0,%1,%2"
  [(set_attr "type" "fadd")
   (set_attr "mode" "<VMODEFLOAT:MODE>")])


(define_insn "<vec_op2u_name><VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
        (vec_op2u:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r,r")
                           (match_operand:VMODEINT 2 "nonmemory_operand" "r,vIusc")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.<vec_op2u_asm_name>.<vec_size> \t%0,%1,%2\t # VectU Op Vect
  pv.<vec_op2u_asm_name>.sci.<vec_size> \t%0,%1,%w2\t # VectU Op Immediate Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "<vec_op2u_name>sc<VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (vec_op2u:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r")
			   (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 2 "register_operand" "r"))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2u_asm_name>.sc.<vec_size> \t%0,%1,%2\t # VectU Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "<vec_op2u_name>_swap_sc<VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (vec_op2u:VMODEINT (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 1 "register_operand" "r"))
		           (match_operand:VMODEINT 2 "register_operand" "r")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2u_asm_name>.sc.<vec_size> \t%0,%2,%1\t # VectU Op Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2s_name><VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
        (vec_op2s:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r,r")
                           (match_operand:<VINT>   2 "nonmemory_operand" "r,vIsdc")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.<vec_op2s_asm_name>.<vec_size> \t%0,%1,%2\t # Vect Shift Vect
  pv.<vec_op2s_asm_name>.sci.<vec_size> \t%0,%1,%W2\t # Vect Shift Immediate Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "<vec_op2s_name>sc<VMODEINT:mode>3"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (vec_op2s:VMODEINT (match_operand:<VINT>   1 "register_operand" "r")
			   (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 2 "register_operand" "r"))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2s_asm_name>.sc.<vec_size> \t%0,%1,%2\t # Vect Shift Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avg<VMODEINT2:mode>3"
  [(set (match_operand:VMODEINT2 0 "register_operand" "=r,r")
	(ashiftrt:VMODEINT2
		(plus:VMODEINT2 (match_operand:VMODEINT2 1 "register_operand" "r,r")
			        (match_operand:VMODEINT2 2 "nonmemory_operand" "r,vIsdc"))
	   	(const_vector:VMODEINT2 [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.avg.<vec_size> \t%0,%1,%2\t # Vect Avg Vect
 pv.avg.sci.<vec_size> \t%0,%1,%W2\t # Vect Avg Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)


(define_insn "avg<VMODEINT4:mode>3"
  [(set (match_operand:VMODEINT4 0 "register_operand" "=r,r")
	(ashiftrt:VMODEINT4
		(plus:VMODEINT4 (match_operand:VMODEINT4 1 "register_operand" "r,r")
			        (match_operand:VMODEINT4 2 "nonmemory_operand" "r,vIsdc"))
	   	(const_vector:VMODEINT4 [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.avg.<vec_size> \t%0,%1,%2\t # Vect Avg Vect
 pv.avg.sci.<vec_size> \t%0,%1,%W2\t # Vect Avg Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "avgsc<VMODEINT2:mode>3"
  [(set (match_operand:VMODEINT2 0 "register_operand" "=r")
	(ashiftrt:VMODEINT2
        	(plus:VMODEINT2 (match_operand:VMODEINT2 1 "register_operand" "r")
			        (vec_duplicate:VMODEINT2 (match_operand:<vec_scalar_elmt> 2 "register_operand" "r")))
	   	(const_vector:VMODEINT2 [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avg.sc.<vec_size> \t%0,%1,%2\t # Vect Avg Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgsc<VMODEINT4:mode>3"
  [(set (match_operand:VMODEINT4 0 "register_operand" "=r")
	(ashiftrt:VMODEINT4
        	(plus:VMODEINT4 (match_operand:VMODEINT4 1 "register_operand" "r")
			        (vec_duplicate:VMODEINT4 (match_operand:<vec_scalar_elmt> 2 "register_operand" "r")))
	   	(const_vector:VMODEINT4 [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avg.sc.<vec_size> \t%0,%1,%2\t # Vect Avg Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgsc_swap_<VMODEINT2:mode>3"
  [(set (match_operand:VMODEINT2 0 "register_operand" "=r")
	(ashiftrt:VMODEINT2
        	(plus:VMODEINT2 (vec_duplicate:VMODEINT2 (match_operand:<vec_scalar_elmt> 1 "register_operand" "r"))
		                (match_operand:VMODEINT2 2 "register_operand" "r"))
	   	(const_vector:VMODEINT2 [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avg.sc.<vec_size> \t%0,%2,%1\t # Vect Avg Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgsc_swap_<VMODEINT4:mode>3"
  [(set (match_operand:VMODEINT4 0 "register_operand" "=r")
	(ashiftrt:VMODEINT4
        	(plus:VMODEINT4 (vec_duplicate:VMODEINT4 (match_operand:<vec_scalar_elmt> 1 "register_operand" "r"))
		                (match_operand:VMODEINT4 2 "register_operand" "r"))
	   	(const_vector:VMODEINT4 [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avg.sc.<vec_size> \t%0,%2,%1\t # Vect Avg Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; Avg unsigned

(define_insn "avgv2uhi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r,r")
	(lshiftrt:V2HI
		(plus:V2HI (match_operand:V2HI 1 "register_operand" "r,r")
			   (match_operand:V2HI 2 "nonmemory_operand" "r,vIusc"))
	   	(const_vector:V2HI [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.avgu.h \t%0,%1,%2\t # Vect2 Avgu Vect
 pv.avgu.sci.h \t%0,%1,%w2\t # Vect2 Avgu Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "avgv4uqi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r,r")
	(lshiftrt:V4QI
		(plus:V4QI (match_operand:V4QI 1 "register_operand" "r,r")
			   (match_operand:V4QI 2 "nonmemory_operand" "r,vIusc"))
	   	(const_vector:V4QI [(const_int 1) (const_int 1)(const_int 1)(const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.avgu.b \t%0,%1,%2\t # Vect4 Avgu Vect
 pv.avgu.sci.b \t%0,%1,%w2\t # Vect4 Avgu Scalar"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "avgscv2uhi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(lshiftrt:V2HI
        	(plus:V2HI (match_operand:V2HI 1 "register_operand" "r")
			   (vec_duplicate:V2HI (match_operand:HI 2 "register_operand" "r")))
	   	(const_vector:V2HI [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avgu.sc.h \t%0,%1,%2\t # Vect 2 AvgU Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgscv4uqi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
	(lshiftrt:V4QI
        	(plus:V4QI (match_operand:V4QI 1 "register_operand" "r")
			   (vec_duplicate:V4QI (match_operand:QI 2 "register_operand" "r")))
	   	(const_vector:V4QI [(const_int 1) (const_int 1)(const_int 1)(const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avgu.sc.b \t%0,%1,%2\t # Vect 4 AvgU Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgsc_swap_v2uhi3"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(lshiftrt:V2HI
        	(plus:V2HI (vec_duplicate:V2HI (match_operand:HI 1 "register_operand" "r"))
		           (match_operand:V2HI 2 "register_operand" "r"))
	   	(const_vector:V2HI [(const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avgu.sc.h \t%0,%2,%1\t # Vect 2 AvgU Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "avgsc_swap_v4uqi3"
  [(set (match_operand:V4QI 0 "register_operand" "=r")
	(lshiftrt:V4QI
        	(plus:V4QI (vec_duplicate:V4QI (match_operand:QI 1 "register_operand" "r"))
		           (match_operand:V4QI 2 "register_operand" "r"))
	   	(const_vector:V4QI [(const_int 1) (const_int 1) (const_int 1) (const_int 1)])
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.avgu.sc.b \t%0,%2,%1\t # Vect 4 AvgU Scalar (swap)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; Logical Instructions

(define_insn "<vec_log2_name><VMODEALL:mode>3"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r,r,xf")
        (vec_log2:VMODEALL (match_operand:VMODEALL 1 "register_operand" "r,r,xf")
                           (match_operand:VMODEALL 2 "nonmemory_operand" "r,vIsdc,xf")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.<vec_log2_asm_name>.<vec_size> \t%0,%1,%2\t # Logical Vect Op Vect
  pv.<vec_log2_asm_name>.sci.<vec_size> \t%0,%1,%W2\t # Logical Vect Op Immediate Scalar
  pv.<vec_log2_asm_name>.<vec_size> \t%0,%1,%2\t # Logical Vect Op Vect"
[(set_attr "type" "logical,logical,logical")
 (set_attr "mode" "SI,SI,SF")]
)

(define_insn "<vec_log2_name>sc<VMODEALL:mode>3"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r,xf")
        (vec_log2:VMODEALL (match_operand:VMODEALL 1 "register_operand" "r,xf")
			   (vec_duplicate:VMODEALL (match_operand:<vec_scalar_elmt> 2 "register_operand" "r,xf"))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_log2_asm_name>.sc.<vec_size> \t%0,%1,%2\t # Logical Vect Op Scalar"
[(set_attr "type" "logical,logical")
 (set_attr "mode" "SI,SF")]
)

(define_insn "<vec_log2_name>_swap_sc<VMODEALL:mode>3"
  [(set (match_operand:VMODEALL 0 "register_operand" "=r,xf")
        (vec_log2:VMODEALL (vec_duplicate:VMODEALL (match_operand:<vec_scalar_elmt> 1 "register_operand" "r,xf"))
		           (match_operand:VMODEALL 2 "register_operand" "r,xf")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.<vec_log2_asm_name>.sc.<vec_size> \t%0,%2,%1\t # Logical Vect Op Scalar (swap)"
[(set_attr "type" "logical,logical")
 (set_attr "mode" "SI,SF")]
)

;; Unary instructions

(define_insn "abs<VMODEFLOAT:mode>2"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
  (abs:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && ((<MODE>mode == V2HFmode && Has_F16) || (<MODE>mode == V2OHFmode && Has_F16ALT))"
  "vfabs.<vec_size>\t%0,%1"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")])

(define_insn "abs<VMODEINT:mode>2"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (abs:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.abs.<vec_size> \t%0,%1\t # Vect abs"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "neg<VMODEFLOAT:mode>2"
  [(set (match_operand:VMODEFLOAT 0 "register_operand" "=xf")
  (neg:VMODEFLOAT (match_operand:VMODEFLOAT 1 "register_operand" "xf")))]
  "TARGET_HARD_FLOAT && ((<MODE>mode == V2HFmode && Has_F16) || (<MODE>mode == V2OHFmode && Has_F16ALT))"
  "vfneg.<vec_size>\t%0,%1"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")])

(define_insn "neg<VMODEINT:mode>2"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
        (neg:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r")
        )
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sub.<vec_size> \t%0,x0,%1\t # Vect neg"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "bitrevsi"
  [(set (match_operand:SI 0 "register_operand"                "=r")
        (unspec:SI [(match_operand:SI 1 "register_operand"  "r")
                    (match_operand:SI 2 "immediate_operand" "i")
                    (match_operand:SI 3 "immediate_operand" "i")
                   ] UNSPEC_BITREV)
   )
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOBITOP && riscv_valid_bitrev_imm_op(operands[3], operands[2]))"
  {
	int Radix, Npoints;
	riscv_bitrev_imm_op(operands[3], operands[2], &Radix, &Npoints);
  	operands[3] = GEN_INT (Radix);
  	operands[2] = GEN_INT (Npoints);
	return "p.bitrev\t%0,%1,%2,%3\t # Bit reverse";
  }
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_low_first"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(vec_concat:V2HI
		(subreg:HI
			(ashiftrt:SI
				(minus:SI
					(mult:SI
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
						)
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
						)
					)
					(mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					)
				)
				(const_int 15)
			) 0
		)
		(const_int 0)
	)
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.h.r \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, real part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_div2_low_first"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(vec_concat:V2HI
		(subreg:HI
			(ashiftrt:SI
				(minus:SI
					(mult:SI
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
						)
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
						)
					)
					(mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					)
				)
				(const_int 16)
			) 0
		)
		(const_int 0)
	)
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.h.r.div2 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div2, real part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "cplxmulsv2hi_div4_low_first"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(vec_concat:V2HI
		(subreg:HI
			(ashiftrt:SI
				(minus:SI
					(mult:SI
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
						)
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
						)
					)
					(mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					)
				)
				(const_int 17)
			) 0
		)
		(const_int 0)
	)
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.h.r.div4 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div4, real part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "cplxmulsv2hi_div8_low_first"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
	(vec_concat:V2HI
		(subreg:HI
			(ashiftrt:SI
				(minus:SI
					(mult:SI
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
						)
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
						)
					)
					(mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					)
				)
				(const_int 18)
			) 0
		)
		(const_int 0)
	)
   )
  ]
"((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.h.r.div8 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div8, real part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_hi"
  [(set	(match_operand:V2HI 0 "register_operand" "=r")
	(vec_merge:V2HI
		(vec_concat:V2HI
			(const_int 0)
			(subreg:HI
				(ashiftrt:SI
					(plus:SI (mult:SI
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 1)])))
					 	)
					 	(mult:SI
							(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
							(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
					 	)
					)
					(const_int 15)
				) 0
			)
		)
          	(match_operand:V2HI 3 "register_operand" "0")
		(const_int 2)
	)
   )
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
  "pv.cplxmul.h.i \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, imaginary part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_div2_hi"
  [(set	(match_operand:V2HI 0 "register_operand" "=r")
	(vec_merge:V2HI
		(vec_concat:V2HI
			(const_int 0)
			(subreg:HI
				(ashiftrt:SI
					(plus:SI (mult:SI
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 1)])))
					 	)
					 	(mult:SI
							(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
							(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
					 	)
					)
					(const_int 16)
				) 0
			)
		)
          	(match_operand:V2HI 3 "register_operand" "0")
		(const_int 2)
	)
   )
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
  "pv.cplxmul.h.i.div2 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div2, imaginary part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_div4_hi"
  [(set	(match_operand:V2HI 0 "register_operand" "=r")
	(vec_merge:V2HI
		(vec_concat:V2HI
			(const_int 0)
			(subreg:HI
				(ashiftrt:SI
					(plus:SI (mult:SI
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 1)])))
					 	)
					 	(mult:SI
							(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
							(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
					 	)
					)
					(const_int 17)
				) 0
			)
		)
          	(match_operand:V2HI 3 "register_operand" "0")
		(const_int 2)
	)
   )
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
  "pv.cplxmul.h.i.div4 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div4, imaginary part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_div8_hi"
  [(set	(match_operand:V2HI 0 "register_operand" "=r")
	(vec_merge:V2HI
		(vec_concat:V2HI
			(const_int 0)
			(subreg:HI
				(ashiftrt:SI
					(plus:SI (mult:SI
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
							(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 1)])))
					 	)
					 	(mult:SI
							(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
							(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
					 	)
					)
					(const_int 18)
				) 0
			)
		)
          	(match_operand:V2HI 3 "register_operand" "0")
		(const_int 2)
	)
   )
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
  "pv.cplxmul.h.i.div8 \t%0,%1,%2\t # Vect/Vect Cplx signed multiply, div8, imaginary part"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_expand "cplxmulsv2hi2"
  [(match_operand:V2HI 0 "register_operand" "")
   (match_operand:V2HI 1 "register_operand" "")
   (match_operand:V2HI 2 "register_operand" "")
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
{
	emit_insn (gen_cplxmulsv2hi_low_first(operands[0], operands[1], operands[2]));
	emit_insn (gen_cplxmulsv2hi_hi       (operands[0], operands[1], operands[2], operands[0]));
  DONE;
})

(define_expand "cplxmulsv2hi2_div2"
  [(match_operand:V2HI 0 "register_operand" "")
   (match_operand:V2HI 1 "register_operand" "")
   (match_operand:V2HI 2 "register_operand" "")
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
{
	emit_insn (gen_cplxmulsv2hi_div2_low_first(operands[0], operands[1], operands[2]));
	emit_insn (gen_cplxmulsv2hi_div2_hi       (operands[0], operands[1], operands[2], operands[0]));
  DONE;
})

(define_expand "cplxmulsv2hi2_div4"
  [(match_operand:V2HI 0 "register_operand" "")
   (match_operand:V2HI 1 "register_operand" "")
   (match_operand:V2HI 2 "register_operand" "")
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
{
	emit_insn (gen_cplxmulsv2hi_div4_low_first(operands[0], operands[1], operands[2]));
	emit_insn (gen_cplxmulsv2hi_div4_hi       (operands[0], operands[1], operands[2], operands[0]));
  DONE;
})

(define_expand "cplxmulsv2hi2_div8"
  [(match_operand:V2HI 0 "register_operand" "")
   (match_operand:V2HI 1 "register_operand" "")
   (match_operand:V2HI 2 "register_operand" "")
  ]
  "((Pulp_Cpu==PULP_GAP9) && !TARGET_MASK_NOVECT)"
{
	emit_insn (gen_cplxmulsv2hi_div8_low_first(operands[0], operands[1], operands[2]));
	emit_insn (gen_cplxmulsv2hi_div8_hi       (operands[0], operands[1], operands[2], operands[0]));
  DONE;
})

/* __GAP8 Start */
;; Complex product

(define_insn "cplxmulsv2hi"
  [(set (match_operand:V2HI 0 "register_operand" "=r,r")
	(vec_concat:V2HI
		(subreg:HI
			(ashiftrt:SI
				(minus:SI
					(mult:SI
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)]))
						)
						(sign_extend:SI
							(vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)]))
						)
					)
					(mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					)
				)
				(const_int 15)
			) 0
		)
		(subreg:HI
			(ashiftrt:SI
				(plus:SI (mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 0)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
					 )
					 (mult:SI
						(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
						(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
					 )
				)
				(const_int 15)
			) 0
		)
	)
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"@
 pv.cplxmul.s \t%0,%1,%2\t # Vect/Vect Cplx signed multiply
 pv.cplxmul.sci.s \t%0,%1,%W2\t # Vect/ScalImm Cplx signed multiply"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "cplxmulsv2hi_div2"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (vec_concat:V2HI
                (subreg:HI
                        (ashiftrt:SI
                                (minus:SI
                                        (mult:SI
                                                (sign_extend:SI
                                                        (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
                                                )
                                                (sign_extend:SI
                                                        (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
                                                )
                                        )
                                        (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
                                        )
                                )
                                (const_int 16)
                        ) 0
                )
                (subreg:HI
                        (ashiftrt:SI
                                (plus:SI (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 0)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
                                         )
                                         (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
                                         )
                                )
                                (const_int 16)
                        ) 0
                )
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.s.div2 \t%0,%1,%2\t # Q15 Vect/Vect Cplx signed multiply >> 1"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "cplxmulsv2hi_div4"
  [(set (match_operand:V2HI 0 "register_operand" "=r")
        (vec_concat:V2HI
                (subreg:HI
                        (ashiftrt:SI
                                (minus:SI
                                        (mult:SI
                                                (sign_extend:SI
                                                        (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
                                                )
                                                (sign_extend:SI
                                                        (vec_select:HI (match_operand:V2HI 2 "register_operand" "r") (parallel [(const_int 0)]))
                                                )
                                        )
                                        (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
                                        )
                                )
                                (const_int 17)
                        ) 0
                )
                (subreg:HI
                        (ashiftrt:SI
                                (plus:SI (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 0)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
                                         )
                                         (mult:SI
                                                (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
                                                (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 0)])))
                                         )
                                )
                                (const_int 17)
                        ) 0
                )
        )
   )
  ]
"((Pulp_Cpu==PULP_GAP8) && !TARGET_MASK_NOVECT)"
"pv.cplxmul.s.div4 \t%0,%1,%2\t # Q15 Vect/Vect Cplx signed multiply >> 2"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; Viterbi Max

(define_insn "vec_vit_max_v2hi"
  [(set (match_operand:V2HI 0 "register_operand"               "=r")
        (unspec:V2HI [(match_operand:V2HI 1 "register_operand" "r")
                      (match_operand:V2HI 2 "register_operand" "r")
                     ] UNSPEC_VIT_MAX)
   )
   (clobber (reg:SI VIT_REG))
  ]
  "((Pulp_Cpu==PULP_GAP8) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.vitop.max \t%0,%1,%2\t # Vect 2 Viterbi max"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; Viterbi Select

(define_insn "vec_vit_sel_v2hi"
  [(set (match_operand:V2HI 0 "register_operand"               "=r")
        (unspec:V2HI [(match_operand:V2HI 1 "register_operand" "r")
                      (match_operand:V2HI 2 "register_operand" "r")
                      (reg:SI VIT_REG)
                     ] UNSPEC_VIT_SEL)
   )
  ]
  "((Pulp_Cpu==PULP_GAP8) && !(TARGET_MASK_NOVECT||TARGET_MASK_NOSHUFFLEPACK))"
  "pv.vitop.sel \t%0,%1,%2\t # Vect 2 Viterbi select"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

/* __GAP8 Stop */


;; Simple dot products


(define_insn "dotpv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(mult:SI
			(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
			(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
		)
		(mult:SI (sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			 (sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
  pv.dotsp.h \t%0,%1,%2\t # Vect 2 dot product
  pv.dotsp.sci.h \t%0,%1,%W2\t # Vect/Imm 2 dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "dotspscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
			(sign_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
		)
		(mult:SI
			(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			(sign_extend:SI (subreg:HI (match_dup 2) 0))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotsp.sc.h \t%0,%1,%2\t # Vect/Scalar reg 2 signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "reduc_plus_scal_v2hi"
  [(set (match_operand:HI 0 "register_operand" "=r")
	(plus:HI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)]))
		 (vec_select:HI (match_dup 1) (parallel [(const_int 1)]))
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotsp.sci.h \t%0,%1,1\t # Vect 2 Sum of elements (reduction)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotupv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
			(zero_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIusc") (parallel [(const_int 0)])))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			(zero_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.dotup.h \t%0,%1,%2\t # Vect 2 unsigned dot product
 pv.dotup.sci.h \t%0,%1,%w2\t # Vect/Imm 2 unsigned dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "dotupscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
			(zero_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			(zero_extend:SI (subreg:HI (match_dup 2) 0))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotup.sc.h \t%0,%1,%2\t # Vect/Scalar reg 2 unssigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotuspv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
			(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.dotusp.h \t%0,%1,%2\t # Vect 2 unsigned/signed dot product
 pv.dotusp.sci.h \t%0,%1,%W2\t # Vect/Imm 2 unsigned/signed dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "dotuspscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
			(sign_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
			(sign_extend:SI (subreg:HI (match_dup 2) 0))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotusp.sc.h \t%0,%1,%2\t # Vect/Scalar reg 2 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotpv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(sign_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
			)
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.dotsp.b \t%0,%1,%2\t # Vect 4 dot product
 pv.dotsp.sci.b \t%0,%1,%W2\t # Vect/Imm 4 dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "reduc_plus_scal_v4qi"
  [(set (match_operand:QI 0 "register_operand" "=r")
	(plus:QI
		(plus:QI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)]))
			 (vec_select:QI (match_dup 1) (parallel [(const_int 1)]))
		)
		(plus:QI (vec_select:QI (match_dup 1) (parallel [(const_int 2)]))
			 (vec_select:QI (match_dup 1) (parallel [(const_int 3)]))
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotsp.sci.b \t%0,%1,1\t # Vect 4 sum of elements (reduction)"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotspscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(sign_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
			(mult:SI
				(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotsp.sc.b \t%0,%1,%2\t # Vect/Scalar reg 4 dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotupv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(zero_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIusc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.dotup.b \t%0,%1,%2\t # Vect 4 unsigned dot product
 pv.dotup.sci.b \t%0,%1,%w2\t # Vect/Imm 4 unsigned dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "dotupscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(zero_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(zero_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(zero_extend:SI (subreg:QI (match_dup 2) 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(zero_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotup.sc.b \t%0,%1,%2\t # Vect/Scalar reg 4 unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotuspv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(sign_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.dotusp.b \t%0,%1,%2\t # Vect 4 unsigned/signed dot product
 pv.dotusp.sci.b \t%0,%1,%W2\t # Vect/Imm 4 unsigned/signed dot product"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "dotuspscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(sign_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
				(sign_extend:SI (subreg:QI (match_dup 2) 0))
			)
		)
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.dotusp.sc.b \t%0,%1,%2\t # Vect/Scalar reg 4 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;; Dot products with accumulation

(define_insn "sdot_prodv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotsp.h \t%0,%1,%2\t # Accumulation of 2 half dot products Vect/Vect
 pv.sdotsp.sci.h \t%0,%1,%W2\t # Accumulation of 2 half dot products vect/Imm"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "sdotspscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(sign_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(sign_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(sign_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (subreg:HI (match_dup 2) 0))
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotsp.sc.h \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 2 signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "udot_prodv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(zero_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIusc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(zero_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotup.h \t%0,%1,%2\t # Accumulation of 2 half unsigned dot products Vect/Vect
 pv.sdotup.sci.h \t%0,%1,%w2\t # Accumulation of 2 half unsigned dot products Vect/Imm"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "sdotupscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(zero_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(zero_extend:SI (subreg:HI (match_dup 2) 0))
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotup.sc.h \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 2 unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotuspv2hi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
				(sign_extend:SI (vec_select:HI (match_operand:V2HI 2 "nonmemory_operand" "r,vIusc") (parallel [(const_int 0)])))
			)
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (vec_select:HI (match_dup 2) (parallel [(const_int 1)])))
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotusp.h \t%0,%1,%2\t # Accumulation of 2 half unsigned/signed dot products Vect/Vect
 pv.sdotusp.sci.h \t%0,%1,%W2\t # Accumulation of 2 half unsigned/signed dot products Vect/Imm"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "sdotuspscv2hi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_operand:V2HI 1 "register_operand" "r") (parallel [(const_int 0)])))
				(sign_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
			)
			(mult:SI
				(zero_extend:SI (vec_select:HI (match_dup 1) (parallel [(const_int 1)])))
				(sign_extend:SI (subreg:HI (match_dup 2) 0))
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotusp.sc.h \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 2 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdot_prodv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
					(sign_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
				)
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
				)
			)
			(plus:SI
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
				)
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotsp.b \t%0,%1,%2\t # Accumulation of 4 byte dot products Vect/Vect
 pv.sdotsp.sci.b \t%0,%1,%W2\t # Accumulation of 4 byte dot products Vect/Imm"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "sdotspscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
					(sign_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
				)
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
			(plus:SI
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
				(mult:SI
					(sign_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotsp.sc.b \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 4 dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "udot_prodv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
					(zero_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIusc") (parallel [(const_int 0)])))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
				)
			)
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(zero_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotup.b \t%0,%1,%2\t # Accumulation of 4 byte unsigned dot products Vect/Vect
 pv.sdotup.sci.b \t%0,%1,%w2\t # Accumulation of 4 byte unsigned dot products Vect/Imm"
[(set_attr "type" "arith,arith")
 (set_attr "mode" "SI,SI")]
)

(define_insn "sdotupscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
					(zero_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(zero_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(zero_extend:SI (subreg:QI (match_dup 2) 0))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(zero_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotup.sc.b \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 4 unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotuspv4qi"
  [(set (match_operand:SI 0 "register_operand" "=r,r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r,r") (parallel [(const_int 0)])))
					(sign_extend:SI (vec_select:QI (match_operand:V4QI 2 "nonmemory_operand" "r,vIsdc") (parallel [(const_int 0)])))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 1)])))
				)
			)
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 2)])))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(sign_extend:SI (vec_select:QI (match_dup 2) (parallel [(const_int 3)])))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0,0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"@
 pv.sdotusp.b \t%0,%1,%2\t # Accumulation of 4 byte unsigned/signed dot products Vect/Vect
 pv.sdotusp.sci.b \t%0,%1,%W2\t # Accumulation of 4 byte unsigned/signed dot products Vect/Imm"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotuspscv4qi_le"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(plus:SI
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_operand:V4QI 1 "register_operand" "r") (parallel [(const_int 0)])))
					(sign_extend:SI (subreg:QI (match_operand:SI 2 "register_operand" "r") 0))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 1)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
			(plus:SI
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 2)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
				(mult:SI
					(zero_extend:SI (vec_select:QI (match_dup 1) (parallel [(const_int 3)])))
					(sign_extend:SI (subreg:QI (match_dup 2) 0))
				)
			)
		)
		(match_operand:SI 3 "register_operand" "0")
	)
   )
  ]
"((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
"pv.sdotusp.sc.b \t%0,%1,%2\t # Accumulation of Vect/Scalar reg 4 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

;;
;;  ....................
;;
;;	VECTOR COMPARISONS
;;
;;  ....................

;; Vector compare

(define_code_iterator vec_cmp_op      		[eq ne le lt ge gt gtu ltu geu leu])
(define_code_iterator vec_cmp_op_s     		[eq ne le lt ge gt])
(define_code_iterator vec_cmp_op_u     		[gtu ltu geu leu])

(define_code_attr vec_cmp_op_name  		[(eq "eq") (ne "ne") (gt "gt") (lt "lt") (ge "ge") (le "le") (gtu "gtu") (ltu "ltu") (geu "geu") (leu "leu")])
(define_code_attr vec_cmp_scal_imm_pref 	[(eq  "W") (ne  "W") (gt  "W") (lt  "W") (ge  "W") (le  "W") (gtu   "w") (ltu   "w") (geu   "w") (leu   "w")])
(define_code_attr vec_cmp_scal_imm_sign 	[(eq  "s") (ne  "s") (gt  "s") (lt  "s") (ge  "s") (le  "s") (gtu   "u") (ltu   "u") (geu   "u") (leu   "u")])
(define_code_attr vec_cmp_swap_op_name 		[(eq "eq") (ne "ne") (gt "lt") (lt "gt") (ge "le") (le "ge") (gtu "ltu") (ltu "gtu") (geu "leu") (leu "geu")])

;; Straight Vector Comparisons Vect/Vect,  Vect/ScalarReg,  Vect/ScalarImm

(define_insn "cmp<VMODEFLOAT:vec_type>_<vec_cmp_op_name>"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (vec_cmp_op_s:<VMODEFLOAT:int_vec_mode>
        	(match_operand:VMODEFLOAT 1 "register_operand" "xf")
                (match_operand:VMODEFLOAT 2 "nonmemory_operand" "xf")
        )
  )]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "vf<vec_cmp_op_name>.<VMODEFLOAT:float_vec_size>\t%0,%1,%2"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")]
)

(define_insn "vec_cmpeq<VMODEFLOAT:vec_type><VMODEFLOAT:int_vec_type>"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (eq:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")
                                      (match_operand:VMODEFLOAT 2 "register_operand" "xf")
        )
  )]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "vfeq.<VMODEFLOAT:float_vec_size>\t%0,%1,%2"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")]
)

(define_insn "cmp<VMODEFLOAT:vec_type>_sc<vec_cmp_op_name>"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (vec_cmp_op:<VMODEFLOAT:int_vec_mode> (match_operand:VMODEFLOAT 1 "register_operand" "xf")
                             		      (vec_duplicate:VMODEFLOAT (match_operand:<vec_scalar_elmt> 2 "register_operand" "xf"))
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "vf<vec_cmp_op_name>.r.<VMODEFLOAT:float_vec_size>\t%0,%1,%2 # cmp vect/scalar op"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")]
)

(define_insn "cmp_swap_<VMODEFLOAT:vec_type>_sc<vec_cmp_op_name>"
  [(set (match_operand:<VMODEFLOAT:int_vec_mode> 0 "register_operand" "=r")
        (vec_cmp_op:<VMODEFLOAT:int_vec_mode> (vec_duplicate:VMODEFLOAT (match_operand:<vec_scalar_elmt> 1 "register_operand" "xf"))
                             		      (match_operand:VMODEFLOAT 2 "register_operand" "xf")
        )
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "vf<vec_cmp_swap_op_name>.r.<VMODEFLOAT:float_vec_size>\t%0,%2,%1 # cmp (swap) vect/scalar op"
  [(set_attr "type" "fadd")
   (set_attr "mode" "SF")]
)


(define_insn "cmp<VMODEINT:vec_type>_<vec_cmp_op_name>"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
	(vec_cmp_op_s:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r,r")
			       (match_operand:VMODEINT 2 "nonmemory_operand" "r,vIsdc")
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "@
  pv.cmp<vec_cmp_op_name>.<VMODEINT:vec_size>\t%0,%1,%2 # cmp vect op
  pv.cmp<vec_cmp_op_name>.sci.<VMODEINT:vec_size>\t%0,%1,%<vec_cmp_scal_imm_pref>2 # cmp vect/imm_scalar op"
  [(set_attr "type" "arith,arith")
   (set_attr "mode" "SI,SI")]
)

(define_insn "cmp<VMODEINT:vec_type>_<vec_cmp_op_name>"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r,r")
	(vec_cmp_op_u:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r,r")
			     (match_operand:VMODEINT 2 "nonmemory_operand" "r,vIusc")
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "@
  pv.cmp<vec_cmp_op_name>.<VMODEINT:vec_size>\t%0,%1,%2 # cmp vect op
  pv.cmp<vec_cmp_op_name>.sci.<VMODEINT:vec_size>\t%0,%1,%<vec_cmp_scal_imm_pref>2 # cmp vect/imm_scalar op"
  [(set_attr "type" "arith,arith")
   (set_attr "mode" "SI,SI")]
)

(define_insn "cmp<VMODEINT:vec_type>_sc<vec_cmp_op_name>"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
	(vec_cmp_op:VMODEINT (match_operand:VMODEINT 1 "register_operand" "r")
			     (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 2 "register_operand" "r"))
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "pv.cmp<vec_cmp_op_name>.sc.<VMODEINT:vec_size>\t%0,%1,%2 # cmp vect/scalar op"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")]
)

(define_insn "cmp_swap_<VMODEINT:vec_type>_sc<vec_cmp_op_name>"
  [(set (match_operand:VMODEINT 0 "register_operand" "=r")
	(vec_cmp_op:VMODEINT (vec_duplicate:VMODEINT (match_operand:<vec_scalar_elmt> 1 "register_operand" "r"))
			     (match_operand:VMODEINT 2 "register_operand" "r")
	)
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  "pv.cmp<vec_cmp_swap_op_name>.sc.<VMODEINT:vec_size>\t%0,%2,%1 # cmp (swap) vect/scalar op"
  [(set_attr "type" "arith")
   (set_attr "mode" "SI")]
)

;; vcond expansion into vector comparisons

(define_expand "vcond<VMODEALL:int_vec_type><mode>"
  [(parallel [
     (set (match_operand:<VMODEALL:int_vec_mode> 0 "register_operand" "")
          (if_then_else:<VMODEALL:int_vec_mode>
		(match_operator 3 "vec_comparison_operator"
            		[(match_operand:VMODEALL 4 "register_operand" "")
             		 (match_operand:VMODEALL 5 "nonmemory_operand" "")]
		)
		(match_operand:<VMODEALL:int_vec_mode> 1 "nonmemory_operand" "")
		(match_operand:<VMODEALL:int_vec_mode> 2 "nonmemory_operand" "")
	  )
     )
     (clobber (match_scratch:<VMODEALL:int_vec_mode> 6 ""))
    ]
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  {
	bool scalar_reg;
	bool simple_form = (riscv_replicated_const_vector(operands[1], -1, -1) && riscv_replicated_const_vector(operands[2], 0, 0));
	rtx target;

	/* Simple form: OP1=-1, OP2=0  OP0 = (OP1 & M) | (OP2 & ^M) where M=CmpOP3(OP4, OP5)  ==> Strictly equivalent to CmpOP3 output */
	/* Non simple form, need to fully implement OP0 = (OP1 & M) | (OP2 & ^M) */
	/* Scratch = CmpOP3(OP4, OP5)
	   O0      = Scratch & O1	Get True part
	   Scratch = Scratch ^ Scratch  Toggle mask
	   Scratch = Scratch & Scratch	Get false part
	   O0      = O0 | Scratch	Merge both parts
        */

	if (simple_form) target = operands[0];
	else {
		rtx reg = gen_reg_rtx (<MODE>mode);
		target = operands[6] = reg;
	}

	if (GET_CODE(operands[4]) == VEC_DUPLICATE) {
		rtx tmp = operands[4];
		operands[4] = operands[5]; operands[5] = tmp;
		PUT_CODE(operands[3], swap_condition(GET_CODE(operands[3])));
	}
	scalar_reg = ((GET_CODE(operands[5]) == VEC_DUPLICATE) && !riscv_replicated_const_vector(XEXP(operands[5], 0), 0, 0));
	switch (GET_CODE(operands[3])) {
		case EQ:
			if (scalar_reg) emit_insn (gen_cmp<mode>_sceq(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_eq(target, operands[4], operands[5]));
			break;
		case NE:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scne(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_ne(target, operands[4], operands[5]));
			break;
		case LT:
			if (scalar_reg) emit_insn (gen_cmp<mode>_sclt(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_lt(target, operands[4], operands[5]));
			break;
		case LE:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scle(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_le(target, operands[4], operands[5]));
			break;
		case GT:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scgt(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_gt(target, operands[4], operands[5]));
			break;
		case GE:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scge(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_ge(target, operands[4], operands[5]));
			break;
		default: abort();
	}
	if (!simple_form) {
  		rtx Vect_m1[4] = {constm1_rtx, constm1_rtx, constm1_rtx, constm1_rtx};
		rtx m1_vect = gen_rtx_CONST_VECTOR (<MODE>mode, gen_rtvec_v (GET_MODE_NUNITS(<MODE>mode), Vect_m1));

		emit_insn( gen_and<vec_type>3(operands[0], target, operands[1]));
		emit_insn(gen_exor<vec_type>3(target,      target, m1_vect));
		emit_insn( gen_and<vec_type>3(target,      target, operands[2]));
		emit_insn( gen_ior<vec_type>3(operands[0], target, operands[0]));
	}
	DONE;
  }
)

;; vcond/vcondu

(define_expand "vcondu<mode><mode>"
  [(parallel [
     (set (match_operand:VMODEINT 0 "register_operand" "")
          (if_then_else:VMODEINT
		(match_operator 3 "vec_comparison_operator"
            		[(match_operand:VMODEINT 4 "register_operand" "")
             		 (match_operand:VMODEINT 5 "nonmemory_operand" "")]
		)
		(match_operand:VMODEINT 1 "nonmemory_operand" "")
		(match_operand:VMODEINT 2 "nonmemory_operand" "")
	  )
     )
     (clobber (match_scratch:VMODEINT 6 ""))
    ]
   )
  ]
  "((Pulp_Cpu>=PULP_V2) && !TARGET_MASK_NOVECT)"
  {
	bool scalar_reg;
	bool simple_form = (riscv_replicated_const_vector(operands[1], -1, -1) && riscv_replicated_const_vector(operands[2], 0, 0));
	rtx target;

	/* Simple form: OP1=-1, OP2=0  OP0 = (OP1 & M) | (OP2 & ^M) where M=CmpOP3(OP4, OP5)  ==> Strictly equivalent to CmpOP3 output */
	/* Non simple form, need to fully implement OP0 = (OP1 & M) | (OP2 & ^M) */
	/* Scratch = CmpOP3(OP4, OP5)
	   O0      = Scratch & O1	Get True part
	   Scratch = Scratch ^ Scratch  Toggle mask
	   Scratch = Scratch & Scratch	Get false part
	   O0      = O0 | Scratch	Merge both parts
        */

	if (simple_form) target = operands[0];
	else {
		rtx reg = gen_reg_rtx (<MODE>mode);
		target = operands[6] = reg;
	}

	if (GET_CODE(operands[4]) == VEC_DUPLICATE) {
		rtx tmp = operands[4];
		operands[4] = operands[5]; operands[5] = tmp;
		PUT_CODE(operands[3], swap_condition(GET_CODE(operands[3])));
	}
	scalar_reg = ((GET_CODE(operands[5]) == VEC_DUPLICATE) && !riscv_replicated_const_vector(XEXP(operands[5], 0), 0, 0));
	switch (GET_CODE(operands[3])) {
		case EQ:
			if (scalar_reg) emit_insn (gen_cmp<mode>_sceq(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_eq(target, operands[4], operands[5]));
			break;
		case NE:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scne(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_ne(target, operands[4], operands[5]));
			break;
		case LT:
		case LTU:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scltu(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_ltu(target, operands[4], operands[5]));
			break;
		case LE:
		case LEU:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scleu(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_leu(target, operands[4], operands[5]));
			break;
		case GT:
		case GTU:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scgtu(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_gtu(target, operands[4], operands[5]));
			break;
		case GE:
		case GEU:
			if (scalar_reg) emit_insn (gen_cmp<mode>_scgeu(target, operands[4], operands[5]));
			else		emit_insn (gen_cmp<mode>_geu(target, operands[4], operands[5]));
			break;
		default: abort();
	}
	if (!simple_form) {
  		rtx Vect_m1[4] = {constm1_rtx, constm1_rtx, constm1_rtx, constm1_rtx};
		rtx m1_vect = gen_rtx_CONST_VECTOR (<MODE>mode, gen_rtvec_v (GET_MODE_NUNITS(<MODE>mode), Vect_m1));

		emit_insn( gen_and<vec_type>3(operands[0], target, operands[1]));
		emit_insn(gen_exor<vec_type>3(target,      target, m1_vect));
		emit_insn( gen_and<vec_type>3(target,      target, operands[2]));
		emit_insn( gen_ior<vec_type>3(operands[0], target, operands[0]));
	}
	DONE;
  }
)

;;
;;  ....................
;;
;;	CONDITIONAL BRANCHES
;;
;;  ....................

;; Conditional branches

(define_insn "*branch_order<mode>"
  [(set (pc)
	(if_then_else
	 (match_operator 1 "order_operator_wo_eq_ne"
			 [(match_operand:X 2 "register_operand" "r")
			  (match_operand:X 3 "register_operand" "r")])
	 (label_ref (match_operand 0 "" ""))
	 (pc)))]
  ""
  "b%C1\t%2,%3,%0"
  [(set_attr "type" "branch")
   (set_attr "mode" "none")])

(define_insn "*branch_zero<mode>"
  [(set (pc)
	(if_then_else
	 (match_operator 1 "signed_order_operator_wo_eq_ne"
			 [(match_operand:X 2 "register_operand" "r")
			  (const_int 0)])
	 (label_ref (match_operand 0 "" ""))
	 (pc)))]
  ""
  "b%C1z\t%2,%0"
  [(set_attr "type" "branch")
   (set_attr "mode" "none")])

(define_insn "*branch_order_eq_ne<mode>"
  [(set (pc)
        (if_then_else
         (match_operator 1 "order_operator_eq_ne"
                 [(match_operand:GPR 2 "register_operand" "r")
                  (match_operand:GPR 3 "reg_or_imm5_operand" "rJYM")])
         (label_ref (match_operand 0 "" ""))
         (pc)))]
  ""
{
  if (GET_CODE (operands[3]) == CONST_INT) {
    if ((INTVAL(operands[3]) != 0) && (INTVAL(operands[3])>=-16) && (INTVAL(operands[3])<=15)) {
        return "p.b%C1imm\t%2,%3,%0";
    } else return "b%C1z\t%2,%0";
  } return "b%C1\t%2,%3,%0";
}
  [(set_attr "type" "branch")
   (set_attr "mode" "none")])

;; Used to implement built-in functions.
(define_expand "condjump"
  [(set (pc)
	(if_then_else (match_operand 0)
		      (label_ref (match_operand 1))
		      (pc)))])

(define_expand "cbranch<mode>4"
  [(set (pc)
	(if_then_else (match_operator 0 "comparison_operator"
		      [(match_operand:BR 1 "register_operand")
		       (match_operand:BR 2 "nonmemory_operand")])
		      (label_ref (match_operand 3 ""))
		      (pc)))]
  ""
{
  riscv_expand_conditional_branch (operands[3], GET_CODE (operands[0]),
				   operands[1], operands[2]);
  DONE;
})

(define_expand "cbranch<mode>4"
  [(set (pc)
        (if_then_else (match_operator 0 "fp_branch_comparison"
                       [(match_operand:SCALARF 1 "register_operand")
                        (match_operand:SCALARF 2 "register_operand")])
                      (label_ref (match_operand 3 ""))
                      (pc)))]
  "TARGET_HARD_FLOAT && (<MODE>mode == SFmode || <MODE>mode == DFmode || (<MODE>mode == OHFmode && Has_F16ALT) || (<MODE>mode == HFmode && Has_F16))"
{
  riscv_expand_conditional_branch (operands[3], GET_CODE (operands[0]),
                                   operands[1], operands[2]);
  DONE;
})

(define_insn_and_split "*branch_on_bit<X:mode>"
  [(set (pc)
	(if_then_else
	    (match_operator 0 "equality_operator"
	        [(zero_extract:X (match_operand:X 2 "register_operand" "r")
				 (const_int 1)
				 (match_operand 3 "branch_on_bit_operand"))
				 (const_int 0)])
	    (label_ref (match_operand 1))
	    (pc)))
   (clobber (match_scratch:X 4 "=&r"))]
  ""
  "#"
  "reload_completed"
  [(set (match_dup 4)
	(ashift:X (match_dup 2) (match_dup 3)))
   (set (pc)
	(if_then_else
	    (match_op_dup 0 [(match_dup 4) (const_int 0)])
	    (label_ref (match_operand 1))
	    (pc)))]
{
  int shift = GET_MODE_BITSIZE (<MODE>mode) - 1 - INTVAL (operands[3]);
  operands[3] = GEN_INT (shift);

  if (GET_CODE (operands[0]) == EQ)
    operands[0] = gen_rtx_GE (<MODE>mode, operands[4], const0_rtx);
  else
    operands[0] = gen_rtx_LT (<MODE>mode, operands[4], const0_rtx);
})

(define_insn_and_split "*branch_on_bit_range<X:mode>"
  [(set (pc)
	(if_then_else
	    (match_operator 0 "equality_operator"
		[(zero_extract:X (match_operand:X 2 "register_operand" "r")
				 (match_operand 3 "branch_on_bit_operand")
				 (const_int 0))
				 (const_int 0)])
	    (label_ref (match_operand 1))
	    (pc)))
   (clobber (match_scratch:X 4 "=&r"))]
  ""
  "#"
  "reload_completed"
  [(set (match_dup 4)
	(ashift:X (match_dup 2) (match_dup 3)))
   (set (pc)
	(if_then_else
	    (match_op_dup 0 [(match_dup 4) (const_int 0)])
	    (label_ref (match_operand 1))
	    (pc)))]
{
  operands[3] = GEN_INT (GET_MODE_BITSIZE (<MODE>mode) - INTVAL (operands[3]));
})

;;
;;  ....................
;;
;;	SETTING A REGISTER FROM A COMPARISON
;;
;;  ....................

;; Destination is always set in SI mode.

(define_expand "cstore<mode>4"
  [(set (match_operand:SI 0 "register_operand")
	(match_operator:SI 1 "order_operator"
	    [(match_operand:GPR 2 "register_operand")
	     (match_operand:GPR 3 "nonmemory_operand")]))]
  ""
{
  riscv_expand_int_scc (operands[0], GET_CODE (operands[1]), operands[2],
			operands[3]);
  DONE;
})

(define_expand "cstore<mode>4"
  [(set (match_operand:SI 0 "register_operand")
	(match_operator:SI 1 "fp_scc_comparison"
	     [(match_operand:ANYF 2 "register_operand")
	      (match_operand:ANYF 3 "register_operand")]))]
  "TARGET_HARD_FLOAT"
{
  riscv_expand_float_scc (operands[0], GET_CODE (operands[1]), operands[2],
			  operands[3]);
  DONE;
})

(define_insn "*cstore<ANYF:mode><X:mode>4"
   [(set (match_operand:X         0 "register_operand" "=r")
	 (match_operator:X 1 "fp_native_comparison"
	     [(match_operand:ANYF 2 "register_operand" " f")
	      (match_operand:ANYF 3 "register_operand" " f")]))]
  "TARGET_HARD_FLOAT"
  { return (Pulp_DP_Format==PULP_DP_FORMAT32) ? "f%C1.s\t%0,%2,%3" : "f%C1.<fmt>\t%0,%2,%3"; }
  [(set_attr "type" "fcmp")
   (set_attr "mode" "<UNITMODE>")])

(define_insn "f<quiet_pattern>_quiet<ANYF:mode><X:mode>4"
   [(set (match_operand:X         0 "register_operand" "=r")
	 (unspec:X
	     [(match_operand:ANYF 1 "register_operand" " f")
	      (match_operand:ANYF 2 "register_operand" " f")]
	     QUIET_COMPARISON))
    (clobber (match_scratch:X 3 "=&r"))]
  "TARGET_HARD_FLOAT"
  "frflags\t%3\n\tf<quiet_pattern>.<fmt>\t%0,%1,%2\n\tfsflags %3"
  [(set_attr "type" "fcmp")
   (set_attr "mode" "<UNITMODE>")
   (set (attr "length") (const_int 12))])

(define_insn "*seq_zero_<X:mode><GPR:mode>"
  [(set (match_operand:GPR       0 "register_operand" "=r")
	(eq:GPR (match_operand:X 1 "register_operand" " r")
		(const_int 0)))]
  ""
  "seqz\t%0,%1"
  [(set_attr "type" "slt")
   (set_attr "mode" "<X:MODE>")])

(define_insn "*sne_zero_<X:mode><GPR:mode>"
  [(set (match_operand:GPR       0 "register_operand" "=r")
	(ne:GPR (match_operand:X 1 "register_operand" " r")
		(const_int 0)))]
  ""
  "snez\t%0,%1"
  [(set_attr "type" "slt")
   (set_attr "mode" "<X:MODE>")])

(define_insn "*sgt<u>_<X:mode><GPR:mode>"
  [(set (match_operand:GPR           0 "register_operand" "= r")
	(any_gt:GPR (match_operand:X 1 "register_operand" "  r")
		    (match_operand:X 2 "reg_or_0_operand" " rJ")))]
  ""
  "sgt<u>\t%0,%1,%z2"
  [(set_attr "type" "slt")
   (set_attr "mode" "<X:MODE>")])

(define_insn "*sge<u>_<X:mode><GPR:mode>"
  [(set (match_operand:GPR           0 "register_operand" "=r")
	(any_ge:GPR (match_operand:X 1 "register_operand" " r")
		    (const_int 1)))]
  ""
  "slt<u>\t%0,zero,%1"
  [(set_attr "type" "slt")
   (set_attr "mode" "<MODE>")])

(define_insn "*slt<u>_<X:mode><GPR:mode>"
  [(set (match_operand:GPR           0 "register_operand" "= r")
	(any_lt:GPR (match_operand:X 1 "register_operand" "  r")
		    (match_operand:X 2 "arith_operand"    " rI")))]
  ""
  "slt<u>\t%0,%1,%2"
  [(set_attr "type" "slt")
   (set_attr "mode" "<MODE>")])

(define_insn "*sle<u>_<X:mode><GPR:mode>"
  [(set (match_operand:GPR           0 "register_operand" "=r")
	(any_le:GPR (match_operand:X 1 "register_operand" " r")
		    (match_operand:X 2 "sle_operand" "")))]
  ""
{
  operands[2] = GEN_INT (INTVAL (operands[2]) + 1);
  return "slt<u>\t%0,%1,%2";
}
  [(set_attr "type" "slt")
   (set_attr "mode" "<MODE>")])

(define_insn "*slet<u>_sisi"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (any_le:SI (match_operand:SI 1 "register_operand" "r")
                   (match_operand:SI 2 "register_operand" "r")))]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOSLET)"
  "p.slet<u>\t%0,%1,%2"
  [(set_attr "type" "slt")
   (set_attr "mode" "SI")])

(define_insn "*sget<u>_sisi"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (any_ge:SI (match_operand:SI 1 "register_operand" "r")
                   (match_operand:SI 2 "register_operand" "r")))]
  "((Pulp_Cpu>=PULP_V0 || Pulp_Cpu==PULP_IMG) && !TARGET_MASK_NOSLET)"
  "p.slet<u>\t%0,%2,%1"
  [(set_attr "type" "slt")
   (set_attr "mode" "SI")])

;;
;;  ....................
;;
;;	UNCONDITIONAL BRANCHES
;;
;;  ....................

;; Unconditional branches.

(define_insn "jump"
  [(set (pc)
	(label_ref (match_operand 0 "" "")))]
  ""
  "j\t%l0"
  [(set_attr "type"	"jump")
   (set_attr "mode"	"none")])

(define_expand "indirect_jump"
  [(set (pc) (match_operand 0 "register_operand"))]
  ""
{
  operands[0] = force_reg (Pmode, operands[0]);
  if (Pmode == SImode)
    emit_jump_insn (gen_indirect_jumpsi (operands[0]));
  else
    emit_jump_insn (gen_indirect_jumpdi (operands[0]));
  DONE;
})

(define_insn "indirect_jump<mode>"
  [(set (pc) (match_operand:P 0 "register_operand" "l"))]
  ""
  "jr\t%0"
  [(set_attr "type" "jump")
   (set_attr "mode" "none")])

(define_expand "tablejump"
  [(set (pc) (match_operand 0 "register_operand" ""))
	      (use (label_ref (match_operand 1 "" "")))]
  ""
{
  if (CASE_VECTOR_PC_RELATIVE)
      operands[0] = expand_simple_binop (Pmode, PLUS, operands[0],
					 gen_rtx_LABEL_REF (Pmode, operands[1]),
					 NULL_RTX, 0, OPTAB_DIRECT);

  if (CASE_VECTOR_PC_RELATIVE && Pmode == DImode)
    emit_jump_insn (gen_tablejumpdi (operands[0], operands[1]));
  else
    emit_jump_insn (gen_tablejumpsi (operands[0], operands[1]));
  DONE;
})

(define_insn "tablejump<mode>"
  [(set (pc) (match_operand:GPR 0 "register_operand" "l"))
   (use (label_ref (match_operand 1 "" "")))]
  ""
  "jr\t%0"
  [(set_attr "type" "jump")
   (set_attr "mode" "none")])

;;
;;  ....................
;;
;;	Function prologue/epilogue
;;
;;  ....................
;;

(define_expand "prologue"
  [(const_int 1)]
  ""
{
  riscv_expand_prologue ();
  DONE;
})

;; Block any insns from being moved before this point, since the
;; profiling call to mcount can use various registers that aren't
;; saved or used to pass arguments.

(define_insn "blockage"
  [(unspec_volatile [(const_int 0)] UNSPECV_BLOCKAGE)]
  ""
  ""
  [(set_attr "type" "ghost")
   (set_attr "mode" "none")])

(define_expand "epilogue"
  [(const_int 2)]
  ""
{
  riscv_expand_epilogue (false);
  DONE;
})

(define_expand "sibcall_epilogue"
  [(const_int 2)]
  ""
{
  riscv_expand_epilogue (true);
  DONE;
})

;; Trivial return.  Make it look like a normal return insn as that
;; allows jump optimizations to work better.

(define_expand "return"
  [(simple_return)]
  "riscv_can_use_return_insn ()"
  "")

(define_insn "simple_return"
  [(simple_return)]
  ""
  "ret"
  [(set_attr "type"	"jump")
   (set_attr "mode"	"none")])

;; Normal return.

(define_insn "simple_return_internal"
  [(simple_return)
   (use (match_operand 0 "pmode_register_operand" ""))]
  ""
  "jr\t%0"
  [(set_attr "type"	"jump")
   (set_attr "mode"	"none")])

(define_insn "simple_it_return"
  [(return)]
  ""
  "eret"
  [(set_attr "type"     "jump")
   (set_attr "mode"     "none")])

(define_insn "simple_itu_return"
  [(unspec [(return)] UNSPEC_ITU)]
  ""
  "uret"
  [(set_attr "type"     "jump")
   (set_attr "mode"     "none")])

(define_insn "simple_its_return"
  [(unspec [(return)] UNSPEC_ITS)]
  ""
  "sret"
  [(set_attr "type"     "jump")
   (set_attr "mode"     "none")])

(define_insn "simple_ith_return"
  [(unspec [(return)] UNSPEC_ITH)]
  "(Pulp_Cpu>=PULP_V2)"
  "hret"
  [(set_attr "type"     "jump")
   (set_attr "mode"     "none")])

(define_insn "simple_itm_return"
  [(unspec [(return)] UNSPEC_ITM)]
  ""
  "mret"
  [(set_attr "type"     "jump")
   (set_attr "mode"     "none")])

;; This is used in compiling the unwind routines.
(define_expand "eh_return"
  [(use (match_operand 0 "general_operand"))]
  ""
{
  if (GET_MODE (operands[0]) != word_mode)
    operands[0] = convert_to_mode (word_mode, operands[0], 0);
  if (TARGET_64BIT)
    emit_insn (gen_eh_set_lr_di (operands[0]));
  else
    emit_insn (gen_eh_set_lr_si (operands[0]));
  DONE;
})

;; Clobber the return address on the stack.  We can't expand this
;; until we know where it will be put in the stack frame.

(define_insn "eh_set_lr_si"
  [(unspec [(match_operand:SI 0 "register_operand" "r")] UNSPEC_EH_RETURN)
   (clobber (match_scratch:SI 1 "=&r"))]
  "! TARGET_64BIT"
  "#")

(define_insn "eh_set_lr_di"
  [(unspec [(match_operand:DI 0 "register_operand" "r")] UNSPEC_EH_RETURN)
   (clobber (match_scratch:DI 1 "=&r"))]
  "TARGET_64BIT"
  "#")

(define_split
  [(unspec [(match_operand 0 "register_operand")] UNSPEC_EH_RETURN)
   (clobber (match_scratch 1))]
  "reload_completed"
  [(const_int 0)]
{
  riscv_set_return_address (operands[0], operands[1]);
  DONE;
})

;; Hardware loops
;;

(define_insn "set_hwloop_lpstart"
 [(set (match_operand:SI 0 "ls_register_operand" "=u")
       (label_ref (match_operand 1 "" ""))
  )
  (use (match_operand:SI 2 "immediate_operand" "I"))
 ]
 ""
 "lp.starti\tx%2,%1\t # loop setup, start set"
 [(set_attr "type" "move")
  (set_attr "mode" "SI")]
)

(define_insn "set_hwloop_lpend"
 [(set (match_operand:SI 0 "le_register_operand" "=t")
       (label_ref (match_operand 1 "" ""))
  )
  (use (match_operand:SI 2 "immediate_operand" "I"))
 ]
 ""
 "lp.endi \tx%2,(%1)\t # loop setup, end set"
 [(set_attr "type" "move")
  (set_attr "mode" "SI")]
)

;; (define_insn "set_hwloop_lc"
;; [(set (match_operand:SI 0 "lc_register_operand" "=k,k")
;;       (unspec_volatile:SI [(match_operand:SI 1 "general_operand" "r,I")] UNSPECV_LC_SET))
;;  (use (match_operand:SI 2 "immediate_operand" "I,I"))
;; ]
;; ""
;; "@
;;  lp.count  \tx%2,%1\t # loop setup, lc set
;;  lp.counti \tx%2,%1\t # loop setup, lc set"
;; [(set_attr "type" "move,move")
;;  (set_attr "mode" "SI")]
;;)

(define_insn "set_hwloop_lc"
 [(set (match_operand:SI 0 "lc_register_operand" "=k,k")
       (unspec_volatile:SI [(match_operand:SI 1 "general_operand" "r,I")] UNSPECV_LC_SET))
  (use (match_operand:SI 2 "immediate_operand" "I,I"))
 ]
 ""
 {
        switch (which_alternative) {
                case 0: return Hw_Loop_Align?".align 2\n\tlp.count  \tx%2,%1\t # loop setup, lc set":"lp.count  \tx%2,%1\t # loop setup, lc set";
		case 1: return Hw_Loop_Align?".align 2\n\tlp.counti \tx%2,%1\t # loop setup, lc set":"lp.counti \tx%2,%1\t # loop setup, lc set";
		default: return "";
	}
 }
 [(set_attr "type" "move,move")
  (set_attr "mode" "SI")]
)

;;(define_insn "set_hwloop_lc_le"
;; [(set (match_operand:SI 0 "lc_register_operand" "=k,k")
;;       (unspec_volatile:SI [(match_operand:SI 1 "general_operand" "r,I")] UNSPECV_LC_SET))
;;  (set (match_operand:SI 2 "le_register_operand" "=t,t")
;;       (label_ref (match_operand 3 "" "")))
;;  (use (match_operand:SI 4 "immediate_operand" "I,I"))
;; ]
;; ""
;; "@
;;  lp.setup  \tx%4,%1,(%3)\t # loop setup, lc+le set
;;  lp.setupi \tx%4,%1,(%3)\t # loop setup, lc+le set"
;; [(set_attr "type" "move,move")
;;  (set_attr "mode" "SI")]
;;)


(define_insn "set_hwloop_lc_le"
 [(set (match_operand:SI 0 "lc_register_operand" "=k,k")
       (unspec_volatile:SI [(match_operand:SI 1 "general_operand" "r,I")] UNSPECV_LC_SET))
  (set (match_operand:SI 2 "le_register_operand" "=t,t")
       (label_ref (match_operand 3 "" "")))
  (use (match_operand:SI 4 "immediate_operand" "I,I"))
 ]
 ""
{
        switch (which_alternative) {
  		case 0: return Hw_Loop_Align?".align 2\n\tlp.setup  \tx%4,%1,(%3)\t # loop setup, lc+le set":"lp.setup  \tx%4,%1,(%3)\t # loop setup, lc+le set";
  		case 1: return Hw_Loop_Align?".align 2\n\tlp.setupi \tx%4,%1,(%3)\t # loop setup, lc+le set":"lp.setupi \tx%4,%1,(%3)\t # loop setup, lc+le set";
		default: return "";
	}
}
 [(set_attr "type" "move,move")
  (set_attr "mode" "SI")]
)

(define_insn "hw_loop_prolog"
 [(set (match_operand:SI 0 "register_operand" "=r")
       (unspec_volatile: SI [(match_operand:SI 1 "immediate_operand" "I")] UNSPECV_ALLOC))
 ]
 ""
 " # HW Loop prolog"
 [(set_attr "type" "move")
  (set_attr "mode" "SI")]
)

(define_insn "zero_cost_loop_end"
   [(set (pc)
        (if_then_else (ne (match_operand:SI 2 "nonimmediate_operand" "0,0")
                          (const_int 1))
                      (label_ref (match_operand 1 "" ""))
                      (pc)))
   (set (match_operand:SI 0 "nonimmediate_operand" "=r,m")
        (plus (match_dup 2)
              (const_int -1)))
   (unspec [(const_int 0)] UNSPEC_LSETUP_END)
   (clobber (match_scratch:SI 3 "=X,&r"))]
  "(Pulp_Cpu>=PULP_V1) && !TARGET_MASK_NOHWLOOP && optimize"
  "#"
  [(set_attr "length" "0")]
;;  [(set_attr "type"   "branch")
;;   (set_attr "mode"   "none")]
)

(define_split
  [(set (pc)
        (if_then_else (ne (match_operand:SI 2 "nonimmediate_operand" "")
                          (const_int 1))
                      (label_ref (match_operand 1 "" ""))
                      (pc)))
   (set (match_operand:SI 0 "nonimmediate_operand" "")
        (plus:SI (match_dup 2)
                 (const_int -1)))
   (unspec [(const_int 0)] UNSPEC_LSETUP_END)
   (clobber (match_scratch 3))]
  "(Pulp_Cpu>=PULP_V1) && !TARGET_MASK_NOHWLOOP && reload_completed"
  [(const_int 0)]
{
  if (!REG_P (operands[0]))
    {
      rtx test;

      /* Fallback into a normal conditional branch insn.  */
      emit_move_insn (operands[3], operands[0]);
      emit_insn (gen_addsi3 (operands[3], operands[3], constm1_rtx));
      emit_move_insn (operands[0], operands[3]);
      test = gen_rtx_NE (VOIDmode, operands[3], const0_rtx);
      emit_jump_insn (gen_cbranchsi4 (test, operands[3],
                                      const0_rtx, operands[1]));
    }
  else
    {
      emit_jump_insn (gen_loop_end (operands[0], operands[1], operands[2]));
    }

  DONE;
})




;; operand 0 is the loop count pseudo register
;; operand 1 is the label to jump to at the top of the loop
(define_expand "doloop_end"
  [(parallel [(set (pc) (if_then_else
                          (ne (match_operand:SI 0 "" "")
                              (const_int 1))
                          (label_ref (match_operand 1 "" ""))
                          (pc)))
              (set (match_dup 0) (plus:SI (match_dup 0) (const_int -1)))
              (unspec [(const_int 0)] UNSPEC_LSETUP_END)
              (clobber (match_dup 2))
            ])]
  ""
{
  /* The loop optimizer doesn't check the predicates... */
  if (GET_MODE (operands[0]) != SImode)
    FAIL;
  riscv_hardware_loop ();
  operands[2]= gen_rtx_SCRATCH(SImode);
})

(define_insn "loop_end"
  [(set (pc)
        (if_then_else (ne (match_operand:SI 2 "register_operand" "0")
                          (const_int 1))
                      (label_ref (match_operand 1 "" ""))
                      (pc)))
   (set (match_operand:SI 0 "register_operand" "=r") (plus (match_dup 2) (const_int -1)))
   (unspec [(const_int 0)] UNSPEC_LSETUP_END)]
 "((Pulp_Cpu>=PULP_V1) && !TARGET_MASK_NOHWLOOP)"
 "/* loop end %0 %l1 */ "
  [(set_attr "length" "0")]
;; [(set_attr "type" "branch")
;;  (set_attr "mode" "none")
;; ]
)
;;
;;  ....................
;;
;;	FUNCTION CALLS
;;
;;  ....................

(define_expand "sibcall"
  [(parallel [(call (match_operand 0 "")
		    (match_operand 1 ""))
	      (use (match_operand 2 ""))	;; next_arg_reg
	      (use (match_operand 3 ""))])]	;; struct_value_size_rtx
  ""
{
  rtx target = riscv_legitimize_call_address (XEXP (operands[0], 0));
  emit_call_insn (gen_sibcall_internal (target, operands[1]));
  DONE;
})

(define_insn "sibcall_internal"
  [(call (mem:SI (match_operand 0 "call_insn_operand" "j,S,U"))
	 (match_operand 1 "" ""))]
  "SIBLING_CALL_P (insn)"
  "@
   jr\t%0
   tail\t%0
   tail\t%0@plt"
  [(set_attr "type" "call")])

(define_expand "sibcall_value"
  [(parallel [(set (match_operand 0 "")
		   (call (match_operand 1 "")
			 (match_operand 2 "")))
	      (use (match_operand 3 ""))])]		;; next_arg_reg
  ""
{
  rtx target = riscv_legitimize_call_address (XEXP (operands[1], 0));
  emit_call_insn (gen_sibcall_value_internal (operands[0], target, operands[2]));
  DONE;
})

(define_insn "sibcall_value_internal"
  [(set (match_operand 0 "" "")
	(call (mem:SI (match_operand 1 "call_insn_operand" "j,S,U"))
	      (match_operand 2 "" "")))]
  "SIBLING_CALL_P (insn)"
  "@
   jr\t%1
   tail\t%1
   tail\t%1@plt"
  [(set_attr "type" "call")])

(define_expand "call"
  [(parallel [(call (match_operand 0 "")
		    (match_operand 1 ""))
	      (use (match_operand 2 ""))	;; next_arg_reg
	      (use (match_operand 3 ""))])]	;; struct_value_size_rtx
  ""
{
  rtx target = riscv_legitimize_call_address (XEXP (operands[0], 0));
  emit_call_insn (gen_call_internal (target, operands[1]));
  DONE;
})

(define_insn "call_internal"
  [(call (mem:SI (match_operand 0 "call_insn_operand" "l,S,U"))
	 (match_operand 1 "" ""))
   (clobber (reg:SI RETURN_ADDR_REGNUM))]
  ""
  "@
   jalr\t%0
   call\t%0
   call\t%0@plt"
  [(set_attr "type" "call")])

(define_expand "call_value"
  [(parallel [(set (match_operand 0 "")
		   (call (match_operand 1 "")
			 (match_operand 2 "")))
	      (use (match_operand 3 ""))])]		;; next_arg_reg
  ""
{
  rtx target = riscv_legitimize_call_address (XEXP (operands[1], 0));
  emit_call_insn (gen_call_value_internal (operands[0], target, operands[2]));
  DONE;
})

(define_insn "call_value_internal"
  [(set (match_operand 0 "" "")
	(call (mem:SI (match_operand 1 "call_insn_operand" "l,S,U"))
	      (match_operand 2 "" "")))
   (clobber (reg:SI RETURN_ADDR_REGNUM))]
  ""
  "@
   jalr\t%1
   call\t%1
   call\t%1@plt"
  [(set_attr "type" "call")])

;; Call subroutine returning any type.

(define_expand "untyped_call"
  [(parallel [(call (match_operand 0 "")
		    (const_int 0))
	      (match_operand 1 "")
	      (match_operand 2 "")])]
  ""
{
  int i;

  emit_call_insn (gen_call (operands[0], const0_rtx, NULL, const0_rtx));

  for (i = 0; i < XVECLEN (operands[2], 0); i++)
    {
      rtx set = XVECEXP (operands[2], 0, i);
      riscv_emit_move (SET_DEST (set), SET_SRC (set));
    }

  emit_insn (gen_blockage ());
  DONE;
})

(define_insn "nop"
  [(const_int 0)]
  ""
  "nop"
  [(set_attr "type"	"nop")
   (set_attr "mode"	"none")])

;; A nop which stays there when emitted.
(define_insn "forced_nop"
  [(unspec [(const_int 0)] UNSPEC_NOP)]
  ""
  "nop"
  [(set_attr "type"     "nop")
   (set_attr "mode"     "none")])

(define_insn "trap"
  [(trap_if (const_int 1) (const_int 0))]
  ""
  "ebreak")

(define_insn "gpr_save"
  [(unspec_volatile [(match_operand 0 "const_int_operand")] UNSPECV_GPR_SAVE)
   (clobber (reg:SI T0_REGNUM))
   (clobber (reg:SI T1_REGNUM))]
  ""
  { return riscv_output_gpr_save (INTVAL (operands[0])); })

(define_insn "gpr_restore"
  [(unspec_volatile [(match_operand 0 "const_int_operand")] UNSPECV_GPR_RESTORE)]
  ""
  "tail\t__riscv_restore_%0")

(define_insn "gpr_restore_return"
  [(return)
   (use (match_operand 0 "pmode_register_operand" ""))
   (const_int 0)]
  ""
  "")

(define_insn "riscv_frflags"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(unspec_volatile [(const_int 0)] UNSPECV_FRFLAGS))]
  "TARGET_HARD_FLOAT"
  "frflags %0")

(define_insn "riscv_fsflags"
  [(unspec_volatile [(match_operand:SI 0 "csr_operand" "rK")] UNSPECV_FSFLAGS)]
  "TARGET_HARD_FLOAT"
  "fsflags %0")

(define_insn "stack_tie<mode>"
  [(set (mem:BLK (scratch))
	(unspec:BLK [(match_operand:X 0 "register_operand" "r")
		     (match_operand:X 1 "register_operand" "r")]
		    UNSPEC_TIE))]
  ""
  ""
  [(set_attr "length" "0")]
)


;;
;; PulpNN Extension
;;

(define_c_enum "unspec_nn" [
  UNSPEC_NN_VECTOR
  UNSPEC_NN_SCALAR
  UNSPEC_NN_QNT
])

(define_code_iterator vec_op2_smallint    	[plus minus smin smax mult])

(define_mode_iterator VMODESMALLINT   [CV NV])
(define_mode_attr smallint_vec_size   [(CV "c")  (NV "n")])



(define_insn "<vec_op2_name><VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2_smallint:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                               (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2_asm_name>.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2_name>sc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2_smallint:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                               (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN)  && !TARGET_MASK_NOVECT)"
"pv.<vec_op2_asm_name>.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2u_name><VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2u:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2u_asm_name>.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2u_name>sc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2u:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN)  && !TARGET_MASK_NOVECT)"
"pv.<vec_op2u_asm_name>.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2s_name><VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2s:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.<vec_op2s_asm_name>.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_op2s_name>sc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_op2s:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN)  && !TARGET_MASK_NOVECT)"
"pv.<vec_op2s_asm_name>.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_log2_name><VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_log2:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.<vec_log2_asm_name>.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "<vec_log2_name>sc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI (vec_log2:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand"  "r")] UNSPEC_NN_VECTOR)
                                                (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
                        )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN)  && !TARGET_MASK_NOVECT)"
"pv.<vec_log2_asm_name>.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Op Scalar"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "avg<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	   (zero_extend:SI(ashiftrt:VMODESMALLINT
	   	 (plus:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)
		    	                 (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
       )
	     (unspec:VMODESMALLINT [(const_int 1)] UNSPEC_NN_VECTOR)
  	 ))
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.avg.<smallint_vec_size> \t%0,%1,%2\t # Vect Avg Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "avgsc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	   (zero_extend:SI(ashiftrt:VMODESMALLINT
	   	 (plus:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)
		    	                 (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
       )
	     (unspec:VMODESMALLINT [(const_int 1)] UNSPEC_NN_VECTOR)
  	 ))
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.avg.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Avg Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "avgu<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	   (zero_extend:SI(lshiftrt:VMODESMALLINT
	   	 (plus:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)
		    	                 (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)
       )
	     (unspec:VMODESMALLINT [(const_int 1)] UNSPEC_NN_VECTOR)
  	 ))
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.avgu.<smallint_vec_size> \t%0,%1,%2\t # Vect Avg Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "avgusc<VMODESMALLINT:mode>3"
  [(set (match_operand:SI 0 "register_operand" "=r")
	   (zero_extend:SI(lshiftrt:VMODESMALLINT
	   	 (plus:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)
		    	                 (unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_SCALAR)
       )
	     (unspec:VMODESMALLINT [(const_int 1)] UNSPEC_NN_VECTOR)
  	 ))
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.avgu.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect Avg Vect"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "abs<VMODESMALLINT:mode>2"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI
          (abs:VMODESMALLINT (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand" "r")] UNSPEC_NN_VECTOR) )
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.abs.<smallint_vec_size> \t%0,%1\t # Vect abs"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "vec_extract_sext_si_<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (sign_extend:SI
          (vec_select:HI
             (unspec:V2HI [ (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand" "r")] UNSPEC_NN_VECTOR) ] UNSPEC_NN_VECTOR)
             (parallel [(match_operand:SI 2 "immediate_operand" "i")])
          )
        )
   )
  ]
  "((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
  "pv.extract.<smallint_vec_size>\t%0,%1,%2\t # vect extract, with sign ext"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)


(define_insn "vec_extract_zext_si_<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI
          (vec_select:HI
             (unspec:V2HI [ (unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand" "r")] UNSPEC_NN_VECTOR) ] UNSPEC_NN_VECTOR)
             (parallel [(match_operand:SI 2 "immediate_operand" "i")])
          )
        )
   )
  ]
  "((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
  "pv.extractu.<smallint_vec_size>\t%0,%1,%2\t # vect extract, with zero ext"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)

(define_insn "vec_insert_si_<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (unspec:SI [(vec_merge:V2HI
          (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "0")] UNSPEC_NN_VECTOR)] UNSPEC_NN_VECTOR)
          (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2 "nonmemory_operand" "r")] UNSPEC_NN_VECTOR)] UNSPEC_NN_VECTOR)
          (match_operand:SI 3 "immediate_operand" "i")
         )] UNSPEC_NN_VECTOR)
   )]
  "((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.insert.<smallint_vec_size>\t%0,%1,%2\t # Vect insert"
[(set_attr "type" "move")
 (set_attr "mode" "SI")]
)



(define_insn "dotup<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
  	 (plus:SI
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotup.<smallint_vec_size> \t%0,%1,%2\t # Vect 2 unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotupsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(zero_extend:SI (unspec:SI [(match_operand:SI 2 "register_operand" "r")] UNSPEC_NN_SCALAR))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(zero_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	)
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotup.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect/Scalar reg 2 unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "dotsp<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
  	 (plus:SI
  		(mult:SI
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotsp.<smallint_vec_size> \t%0,%1,%2\t # Vect 2 signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotspsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(sign_extend:SI (unspec:SI [(match_operand:SI 2 "register_operand" "r")] UNSPEC_NN_SCALAR))
		)
		(mult:SI
			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(sign_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	)
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotsp.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect/Scalar reg 2 signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotusp<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
  	 (plus:SI
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotusp.<smallint_vec_size> \t%0,%1,%2\t # Vect 2 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "dotuspsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
	(plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(sign_extend:SI (unspec:SI [(match_operand:SI 2 "register_operand" "r")] UNSPEC_NN_SCALAR))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(sign_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	)
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.dotusp.sc.<smallint_vec_size> \t%0,%1,%2\t # Vect/Scalar reg 2 unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)





(define_insn "sdotup<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
  	 (plus:SI
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
         (match_operand:SI 3 "register_operand" "0")
       )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotup.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotupsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
	 (plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(zero_extend:SI (unspec:SI [(match_operand:SI 2 "register_operand" "r")] UNSPEC_NN_SCALAR))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(zero_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	 )
         (match_operand:SI 3 "register_operand" "0")
       )
   )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotup.sc.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect/Scalar reg unsigned dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "sdotsp<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
  	 (plus:SI
  		(mult:SI
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
         (match_operand:SI 3 "register_operand" "0")
       )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotsp.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotspsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
	 (plus:SI
		(mult:SI
			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(sign_extend:SI (subreg:HI (match_operand:SI 2 "register_operand" "r") 0))
		)
		(mult:SI
			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(sign_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	 )
         (match_operand:SI 3 "register_operand" "0")
       )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotsp.sc.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect/Scalar reg signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotusp<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
  	 (plus:SI
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
  		)
  		(mult:SI
  			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR)(parallel [(const_int 1)])))
  			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 2)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
  		)
  	 )
         (match_operand:SI 3 "register_operand" "0")
       )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotusp.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "sdotuspsc<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
       (plus:SI
	 (plus:SI
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_operand:SI 1  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 0)])))
			(sign_extend:SI (unspec:SI [(match_operand:SI 2 "register_operand" "r")] UNSPEC_NN_SCALAR))
		)
		(mult:SI
			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESMALLINT [(match_dup 1)] UNSPEC_NN_VECTOR)]   UNSPEC_NN_VECTOR) (parallel [(const_int 1)])))
			(sign_extend:SI (unspec:SI [(match_dup 2)] UNSPEC_NN_SCALAR))
		)
	 )
         (match_operand:SI 3 "register_operand" "0")
       )
  )]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.sdotusp.sc.<smallint_vec_size> \t%0,%1,%2\t # Accumulation of Vect/Scalar reg unsigned/signed dot product"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "qnt<VMODESMALLINT:mode>"
  [(set (match_operand:SI 0 "register_operand" "=r")
        (zero_extend:SI
          (unspec:VMODESMALLINT [(unspec:VMODESMALLINT [(match_operand:SI 1 "register_operand" "r")] UNSPEC_NN_VECTOR)
                                (match_operand:SI 2 "register_operand" "r")]
           UNSPEC_NN_QNT)
        )
   )
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.qnt.<smallint_vec_size> \t%0,%1,%2\t # Vect abs"
[(set_attr "type" "qnt")
 (set_attr "mode" "SI")]
)

;;
;; PulpNN Extension v2
;;

(define_c_enum "unspec_nn_v2" [
  UNSPEC_MLSDOT_INIT
  UNSPEC_MLSDOT
])

(define_mode_iterator VMODESALLINT   [HV BV CV NV])
(define_mode_attr allint_vec_size   [(HV "h")  (BV "b") (CV "c")  (NV "n")])


(define_insn "mlinitspr"
  [(unspec_volatile [ (match_operand:SI 0 "register_operand" "r") (match_operand:SI 1 "immediate_operand" "L")] UNSPEC_MLSDOT_INIT)
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.mlsdotup.h.%1 \tx0,%0,x0\t"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "mlsdotup<VMODESALLINT:mode>"
  [
    (parallel[
      (use:SI (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
      (set (match_operand:SI 0 "register_operand" "=r")
           (plus:SI
          	 (plus:SI
          		(mult:SI
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1) (match_operand:SI 4 "immediate_operand" "L")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          		)
          		(mult:SI
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT)(parallel [(const_int 1)])))
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 2)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT) (parallel [(const_int 1)])))
          		)
          	 )
             (match_operand:SI 3 "register_operand" "0")
           )
      )
    ])
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.mlsdotup.<allint_vec_size>.%4 \t%0,%1,%2\t"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)


(define_insn "mlsdotusp<VMODESALLINT:mode>"
  [
    (parallel[
      (use:SI (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
      (set (match_operand:SI 0 "register_operand" "=r")
           (plus:SI
          	 (plus:SI
          		(mult:SI
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1) (match_operand:SI 4 "immediate_operand" "L")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          		)
          		(mult:SI
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT)(parallel [(const_int 1)])))
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 2)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT) (parallel [(const_int 1)])))
          		)
          	 )
             (match_operand:SI 3 "register_operand" "0")
           )
      )
    ])
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.mlsdotusp.<allint_vec_size>.%4 \t%0,%1,%2\t"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "mlsdotsup<VMODESALLINT:mode>"
  [
    (parallel[
      (use:SI (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
      (set (match_operand:SI 0 "register_operand" "=r")
           (plus:SI
          	 (plus:SI
          		(mult:SI
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1) (match_operand:SI 4 "immediate_operand" "L")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          		)
          		(mult:SI
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT)(parallel [(const_int 1)])))
          			(zero_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 2)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT) (parallel [(const_int 1)])))
          		)
          	 )
             (match_operand:SI 3 "register_operand" "0")
           )
      )
    ])
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.mlsdotsup.<allint_vec_size>.%4 \t%0,%1,%2\t"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)

(define_insn "mlsdotsp<VMODESALLINT:mode>"
  [
    (parallel[
      (use:SI (post_inc:SI (match_operand:SI 1 "register_operand" "+r")))
      (set (match_operand:SI 0 "register_operand" "=r")
           (plus:SI
          	 (plus:SI
          		(mult:SI
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1) (match_operand:SI 4 "immediate_operand" "L")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_operand:SI 2  "register_operand" "r")] UNSPEC_NN_VECTOR)]   UNSPEC_MLSDOT) (parallel [(const_int 0)])))
          		)
          		(mult:SI
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 1)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT)(parallel [(const_int 1)])))
          			(sign_extend:SI (vec_select:HI (unspec:V2HI [(unspec:VMODESALLINT [(match_dup 2)] UNSPEC_MLSDOT)]   UNSPEC_MLSDOT) (parallel [(const_int 1)])))
          		)
          	 )
             (match_operand:SI 3 "register_operand" "0")
           )
      )
    ])
  ]
"((Pulp_Cpu==PULP_NN) && !TARGET_MASK_NOVECT)"
"pv.mlsdotsp.<allint_vec_size>.%4 \t%0,%1,%2\t"
[(set_attr "type" "arith")
 (set_attr "mode" "SI")]
)




(include "sync.md")
(include "peephole.md")
(include "pic.md")
(include "generic.md")
(include "marsellus0.md")
(include "marsellus1.md")
(include "marsellus2.md")
(include "marsellus3.md")

