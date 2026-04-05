import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Semigroup α] [DecidableEq α]

theorem op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α) :
    op a • s * t = s * a • t := op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

