import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

theorem mul_right_eq_one (x : tsze R M) (r : R) (h : x.fst * r = 1) :
    x * (TrivSqZeroExt.inl r + TrivSqZeroExt.inr (-(r •> (x.snd <• r)))) = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]

