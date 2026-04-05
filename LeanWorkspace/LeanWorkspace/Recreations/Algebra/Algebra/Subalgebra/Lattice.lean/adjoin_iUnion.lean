import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_iUnion {α : Type*} (s : α → Set A) :
    Algebra.adjoin R (Set.iUnion s) = ⨆ i : α, Algebra.adjoin R (s i) := (@Algebra.gc R A _ _ _).l_iSup

