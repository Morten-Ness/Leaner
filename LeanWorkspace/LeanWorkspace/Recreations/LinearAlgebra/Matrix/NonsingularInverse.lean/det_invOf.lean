import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
  letI := Matrix.detInvertibleOfInvertible A
  convert (rfl : _ = ⅟A.det)

