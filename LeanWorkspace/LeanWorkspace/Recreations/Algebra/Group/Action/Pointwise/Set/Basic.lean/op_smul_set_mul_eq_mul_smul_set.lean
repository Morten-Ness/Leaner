import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Semigroup α]

theorem op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t := op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

