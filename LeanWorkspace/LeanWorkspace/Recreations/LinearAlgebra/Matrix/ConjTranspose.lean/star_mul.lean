import Mathlib

variable {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type v} {β : Type w} {γ : Type*}

theorem star_mul [Fintype n] [NonUnitalNonAssocSemiring α] [StarRing α] (M N : Matrix n n α) :
    star (M * N) = star N * star M := Matrix.conjTranspose_mul _ _

