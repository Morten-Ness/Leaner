import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    Algebra.adjoin R s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R s) := Algebra.adjoin_le Set.subset_centralizer_centralizer

