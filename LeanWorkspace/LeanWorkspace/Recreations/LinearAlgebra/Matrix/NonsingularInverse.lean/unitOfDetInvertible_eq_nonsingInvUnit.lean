import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    Matrix.unitOfDetInvertible A = Matrix.nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  rfl

