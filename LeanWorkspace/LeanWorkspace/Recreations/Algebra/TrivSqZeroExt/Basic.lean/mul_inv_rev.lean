import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

variable [SMulCommClass R Rᵐᵒᵖ M]

theorem mul_inv_rev (a b : tsze R M) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  ext
  · rw [fst_inv, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, fst_inv]
    simp only [smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (TrivSqZeroExt.fst a) 0
    · simp [ha0]
    obtain hb0 | hb := eq_or_ne (TrivSqZeroExt.fst b) 0
    · simp [hb0]
    rw [inv_mul_cancel_right₀ ha, mul_inv_cancel_left₀ hb]

