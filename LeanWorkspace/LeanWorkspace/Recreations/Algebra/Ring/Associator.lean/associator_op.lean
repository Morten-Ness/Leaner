import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R]

theorem associator_op (x y z : Rᵐᵒᵖ) :
    associator x y z = -op (associator (unop z) (unop y) (unop x)) := by
  simp only [associator_apply, ← unop_mul, ← unop_sub, op_unop, neg_sub]

