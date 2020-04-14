(define_automaton "marsellus2")

(define_cpu_unit "marsellus2_alu" "marsellus2")
(define_cpu_unit "marsellus2_fdivsqrt" "marsellus2")

(define_insn_reservation "marsellus2_generic_alu" 1
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "unknown,const,arith,shift,slt,multi,nop,logical,move"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_load" 2
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "load,fpload"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_store" 1
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "store,fpstore"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_xfer" 1
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "mfc,mtc,fmove"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_branch" 1
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "branch,jump,call"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_imul" 1
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "imul"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_idivsi" 3
  (and (eq_attr "tune" "marsellus2")
       (and (eq_attr "type" "idiv")
            (eq_attr "mode" "SI")))
  "marsellus2_alu*3")

(define_insn_reservation "marsellus2_generic_fmul_single" 3
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "fadd,fmul,fmadd"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_xfer_float" 3
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "fcvt,fcmp"))
  "marsellus2_alu")

(define_insn_reservation "marsellus2_generic_fdiv" 20
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "fdiv"))
  "marsellus2_fdivsqrt*20")

(define_insn_reservation "marsellus2_generic_fsqrt" 20
  (and (eq_attr "tune" "marsellus2")
       (eq_attr "type" "fsqrt"))
  "marsellus2_fdivsqrt*20")

