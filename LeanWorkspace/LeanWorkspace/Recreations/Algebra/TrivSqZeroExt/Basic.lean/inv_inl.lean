import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

theorem inv_inl (r : R) :
    (TrivSqZeroExt.inl r)⁻¹ = (TrivSqZeroExt.inl (r⁻¹ : R) : tsze R M) := by
  ext
  · rw [fst_inv, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inl]
  · rw [snd_inv, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, smul_zero, smul_zero, neg_zero]

