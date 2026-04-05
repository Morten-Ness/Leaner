import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem mul_inv_rev (A B : Matrix n n α) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  simp only [Matrix.inv_def]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.det_mul, adjugate_mul_distrib,
    Ring.mul_inverse_rev]

