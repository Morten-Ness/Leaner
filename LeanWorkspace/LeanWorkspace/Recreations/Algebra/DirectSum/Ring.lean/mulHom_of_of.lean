import Mathlib

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [Add ι] [∀ i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

theorem mulHom_of_of {i j} (a : A i) (b : A j) :
    DirectSum.mulHom A (of A i a) (of A j b) = of A (i + j) (GradedMonoid.GMul.mul a b) := by
  simp

