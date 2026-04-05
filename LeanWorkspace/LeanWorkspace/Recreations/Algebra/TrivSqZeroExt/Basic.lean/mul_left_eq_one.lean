import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

theorem mul_left_eq_one (r : R) (x : tsze R M) (h : r * x.fst = 1) :
    (TrivSqZeroExt.inl r + TrivSqZeroExt.inr (-((r •> x.snd) <• r))) * x = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]

