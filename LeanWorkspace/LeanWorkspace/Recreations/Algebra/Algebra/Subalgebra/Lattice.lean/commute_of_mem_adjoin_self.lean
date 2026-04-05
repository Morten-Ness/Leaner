import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem commute_of_mem_adjoin_self {a b : A} (hb : b ∈ R[a]) :
    Commute a b := Algebra.commute_of_mem_adjoin_singleton_of_commute hb rfl

