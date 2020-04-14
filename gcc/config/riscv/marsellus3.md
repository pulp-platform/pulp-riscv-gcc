(define_automaton "marsellus3")

(define_cpu_unit "marsellus3_alu" "marsellus3")
(define_cpu_unit "marsellus3_fdivsqrt" "marsellus3")

(define_insn_reservation "marsellus3_generic_alu" 1
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "unknown,const,arith,shift,slt,multi,nop,logical,move"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_load" 2
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "load,fpload"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_store" 1
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "store,fpstore"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_xfer" 1
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "mfc,mtc,fmove"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_branch" 1
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "branch,jump,call"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_imul" 1
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "imul"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_idivsi" 3
  (and (eq_attr "tune" "marsellus3")
       (and (eq_attr "type" "idiv")
            (eq_attr "mode" "SI")))
  "marsellus3_alu*3")

(define_insn_reservation "marsellus3_generic_fmul_single" 4
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "fadd,fmul,fmadd"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_xfer_float" 4
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "fcvt,fcmp"))
  "marsellus3_alu")

(define_insn_reservation "marsellus3_generic_fdiv" 20
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "fdiv"))
  "marsellus3_fdivsqrt*20")

(define_insn_reservation "marsellus3_generic_fsqrt" 20
  (and (eq_attr "tune" "marsellus3")
       (eq_attr "type" "fsqrt"))
  "marsellus3_fdivsqrt*20")

