FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_eq_sInf : Algebra.adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } := by
  exact le_antisymm
    (by
      rw [show Algebra.adjoin R s = sInf { S : Subalgebra R A | Algebra.adjoin R s ≤ S } by
        exact Algebra.adjoin_eq_sInf]
      exact sInf_le (by
        intro x hx
        exact Algebra.subset_adjoin hx))
    (sInf_le (by
      intro x hx
      exact Algebra.subset_adjoin hx))
