import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_span {s : Set A} : Algebra.adjoin R (Submodule.span R s : Set A) = Algebra.adjoin R s := le_antisymm (Algebra.adjoin_le (Algebra.span_le_adjoin _ _)) (Algebra.adjoin_mono Submodule.subset_span)

