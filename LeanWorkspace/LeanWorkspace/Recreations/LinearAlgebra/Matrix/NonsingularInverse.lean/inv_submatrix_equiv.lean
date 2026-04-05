import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

variable [Fintype m]

variable [DecidableEq m]

theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    (A.submatrix e₁ e₂)⁻¹ = A⁻¹.submatrix e₂ e₁ := by
  by_cases h : IsUnit A
  · cases h.nonempty_invertible
    letI := Matrix.submatrixEquivInvertible A e₁ e₂
    rw [← Matrix.invOf_eq_nonsing_inv, ← Matrix.invOf_eq_nonsing_inv, Matrix.invOf_submatrix_equiv_eq A]
  · have := (Matrix.isUnit_submatrix_equiv e₁ e₂).not.mpr h
    simp_rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ this,
      submatrix_zero, Pi.zero_apply]

