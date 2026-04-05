import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_empty : Algebra.adjoin R (∅ : Set A) = ⊥ := Algebra.gc.l_bot

