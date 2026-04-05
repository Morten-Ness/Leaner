import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_sub_inv {A B : Matrix n n α} (h : IsUnit A ↔ IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using Ring.inverse_sub_inverse h

