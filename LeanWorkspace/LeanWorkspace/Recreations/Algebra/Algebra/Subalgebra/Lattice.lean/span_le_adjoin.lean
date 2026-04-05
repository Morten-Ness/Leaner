import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem span_le_adjoin (s : Set A) : span R s ≤ Subalgebra.toSubmodule (Algebra.adjoin R s) := span_le.mpr Algebra.subset_adjoin

