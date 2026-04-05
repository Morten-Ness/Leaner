import Mathlib

variable {R : Type*} (n : Type*)

variable [NonUnitalNonAssocRing R] [Fintype n]

theorem mem_matrix (I : TwoSidedIdeal R) (M : Matrix n n R) :
    M ∈ I.matrix n ↔ ∀ i j, M i j ∈ I := Iff.rfl

