import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq (S : Subalgebra R A) : Algebra.adjoin R ↑S = S := by
  apply le_antisymm
  · exact Algebra.adjoin_le fun x hx => hx
  · intro x hx
    exact Algebra.subset_adjoin hx
