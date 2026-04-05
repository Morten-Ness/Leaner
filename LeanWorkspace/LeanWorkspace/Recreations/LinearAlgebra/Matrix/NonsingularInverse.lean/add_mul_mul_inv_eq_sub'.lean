import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

variable [Fintype m] [DecidableEq m]

variable (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)

theorem add_mul_mul_inv_eq_sub' (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U * C)) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * C * (C + C * V * A⁻¹ * U * C)⁻¹ * C * V * A⁻¹ := by
  obtain ⟨_⟩ := hA.nonempty_invertible
  obtain ⟨ih⟩ := h.nonempty_invertible
  simp only [← Matrix.invOf_eq_nonsing_inv] at ih
  letI := invertibleAddMulMul' A U C V
  simp only [← Matrix.invOf_eq_nonsing_inv]
  apply invOf_add_mul_mul'

