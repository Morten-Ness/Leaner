import Mathlib

variable {α β R n m : Type*}

theorem IsDiag.conjTranspose [NonUnitalNonAssocSemiring α] [StarRing α] {A : Matrix n n α}
    (ha : A.IsDiag) : Aᴴ.IsDiag := ha.transpose.map (star_zero _)

