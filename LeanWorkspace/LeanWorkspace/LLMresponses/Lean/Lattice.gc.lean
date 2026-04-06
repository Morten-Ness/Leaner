import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem gc : GaloisConnection (Algebra.adjoin R : Set A → Subalgebra R A) (↑) := by
  intro s S
  constructor
  · intro hs
    intro x hx
    exact hs (Algebra.subset_adjoin hx)
  · intro hs
    exact Algebra.adjoin_le hs
