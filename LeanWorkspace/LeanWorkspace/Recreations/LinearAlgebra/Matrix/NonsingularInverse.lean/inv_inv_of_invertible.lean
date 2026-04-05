import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_inv_of_invertible [Invertible A] : A⁻¹⁻¹ = A := by
  simp only [← Matrix.invOf_eq_nonsing_inv, invOf_invOf]

