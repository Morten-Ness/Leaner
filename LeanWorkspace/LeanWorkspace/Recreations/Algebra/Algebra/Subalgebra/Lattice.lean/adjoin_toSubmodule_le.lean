import Mathlib

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    Subalgebra.toSubmodule (Algebra.adjoin R s) ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [Algebra.adjoin_eq_span, span_le]

