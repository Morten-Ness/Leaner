import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_apply {c : RingCon R} {M N : Matrix n n R} :
    c.matrix n M N ↔ ∀ i j, c (M i j) (N i j) := Iff.rfl

