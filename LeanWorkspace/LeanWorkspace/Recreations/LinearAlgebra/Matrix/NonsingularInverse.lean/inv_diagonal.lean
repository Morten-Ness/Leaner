import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_diagonal (v : n → α) : (diagonal v)⁻¹ = diagonal v⁻¹ʳ := by
  rw [Matrix.nonsing_inv_eq_ringInverse]
  by_cases h : IsUnit v
  · have := Matrix.isUnit_diagonal.mpr h
    cases this.nonempty_invertible
    cases h.nonempty_invertible
    rw [Ring.inverse_invertible, Ring.inverse_invertible, Matrix.invOf_diagonal_eq]
  · have := Matrix.isUnit_diagonal.not.mpr h
    rw [Ring.inverse_non_unit _ h, Pi.zero_def, diagonal_zero, Ring.inverse_non_unit _ this]

