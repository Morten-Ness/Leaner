import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    Subalgebra.toSubmodule (Algebra.adjoin R s) = span R s := le_antisymm ((Algebra.adjoin_toSubmodule_le R).mpr hs) (Algebra.span_le_adjoin R s)

