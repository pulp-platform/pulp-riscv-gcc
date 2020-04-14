(define_automaton "marsellus0")

(define_cpu_unit "marsellus0_alu" "marsellus0")
(define_cpu_unit "marsellus0_fdivsqrt" "marsellus0")

(define_insn_reservation "marsellus0_generic_alu" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "unknown,const,arith,shift,slt,multi,nop,logical,move"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_load" 2
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "load,fpload"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_store" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "store,fpstore"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_xfer" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "mfc,mtc,fmove"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_branch" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "branch,jump,call"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_imul" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "imul"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_idivsi" 3
  (and (eq_attr "tune" "marsellus0")
       (and (eq_attr "type" "idiv")
            (eq_attr "mode" "SI")))
  "marsellus0_alu*3")

(define_insn_reservation "marsellus0_generic_fmul_single" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "fadd,fmul,fmadd"))
  "marsellus0_alu")

(define_insn_reservation "marsellus0_generic_xfer_float" 1
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "fcvt,fcmp"))
  "marsellus0_alu")



(define_insn_reservation "marsellus0_generic_fdiv" 20
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "fdiv"))
  "marsellus0_fdivsqrt*20")

(define_insn_reservation "marsellus0_generic_fsqrt" 20
  (and (eq_attr "tune" "marsellus0")
       (eq_attr "type" "fsqrt"))
  "marsellus0_fdivsqrt*20")

