;; mempool DFA-based pipeline description for RISC-V targets.
;; Copyright (C) 2011-2018 Free Software Foundation, Inc.
;; Contributed by Andrew Waterman (andrew@sifive.com).
;; Based on MIPS target for GNU compiler.

;; This file is part of GCC.

;; GCC is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; GCC is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;; License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GCC; see the file COPYING3.  If not see
;; <http://www.gnu.org/licenses/>.

(define_automaton "mempool")
(define_cpu_unit "mempool_alu" "mempool")

(define_insn_reservation "mempool_alu" 1
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "unknown,const,arith,shift,slt,multi,nop,logical,move"))
  "mempool_alu")

(define_insn_reservation "mempool_load" 8
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "load,fpload"))
  "mempool_alu,nothing*7")

(define_insn_reservation "mempool_store" 1
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "store,fpstore"))
  "mempool_alu")

(define_insn_reservation "mempool_branch" 1
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "branch,jump,call"))
  "mempool_alu")

(define_insn_reservation "mempool_imul" 3
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "imul"))
  "mempool_alu,nothing*2")

(define_insn_reservation "mempool_idiv" 3
  (and (eq_attr "tune" "mempool")
       (eq_attr "type" "idiv"))
  "mempool_alu,nothing*2")
