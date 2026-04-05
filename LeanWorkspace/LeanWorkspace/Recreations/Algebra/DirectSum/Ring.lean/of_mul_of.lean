import Mathlib

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

theorem of_mul_of {i j} (a : A i) (b : A j) :
    of A i a * of A j b = of _ (i + j) (GradedMonoid.GMul.mul a b) := DirectSum.mulHom_of_of a b

