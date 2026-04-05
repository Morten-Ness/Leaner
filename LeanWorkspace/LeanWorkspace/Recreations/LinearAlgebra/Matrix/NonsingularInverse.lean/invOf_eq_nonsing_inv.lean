import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem invOf_eq_nonsing_inv [Invertible A] : ⅟A = A⁻¹ := by
  letI := Matrix.detInvertibleOfInvertible A
  rw [Matrix.inv_def, Ring.inverse_invertible, Matrix.invOf_eq]

