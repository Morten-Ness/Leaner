import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ Algebra.adjoin R s := Algebra.subset_adjoin hx

