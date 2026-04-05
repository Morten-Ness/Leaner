import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_inr (m : M) : (TrivSqZeroExt.inr m)⁻¹ = (0 : tsze R M) := by
  ext
  · rw [fst_inv, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_zero, inv_zero]
  · rw [snd_inv, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr, inv_zero, op_zero, zero_smul, TrivSqZeroExt.snd_zero, neg_zero]

