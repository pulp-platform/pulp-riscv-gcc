
(define_automaton "marsellus1")

(define_cpu_unit "marsellus1_alu" "marsellus1")
(define_cpu_unit "marsellus1_fdivsqrt" "marsellus1")

(define_insn_reservation "marsellus1_generic_alu" 1
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "unknown,const,arith,shift,slt,multi,nop,logical,move"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_load" 2
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "load,fpload"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_store" 1
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "store,fpstore"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_xfer" 1
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "mfc,mtc,fmove"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_branch" 1
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "branch,jump,call"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_imul" 1
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "imul"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_idivsi" 3
  (and (eq_attr "tune" "marsellus1")
       (and (eq_attr "type" "idiv")
	    (eq_attr "mode" "SI")))
  "marsellus1_alu*3")

(define_insn_reservation "marsellus1_generic_fmul_single" 2
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "fadd,fmul,fmadd"))
  "marsellus1_alu")

(define_insn_reservation "marsellus1_generic_xfer_float" 2
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "fcvt,fcmp"))
  "marsellus1_alu")


(define_insn_reservation "marsellus1_generic_fdiv" 20
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "fdiv"))
  "marsellus1_fdivsqrt*20")

(define_insn_reservation "marsellus1_generic_fsqrt" 20
  (and (eq_attr "tune" "marsellus1")
       (eq_attr "type" "fsqrt"))
  "marsellus1_fdivsqrt*20")
