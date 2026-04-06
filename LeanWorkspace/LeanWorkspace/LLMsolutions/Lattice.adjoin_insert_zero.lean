import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_zero (s : Set A) : Algebra.adjoin R (insert 0 s) = Algebra.adjoin R s := by
  refine le_antisymm ?_ ?_
  · refine Algebra.adjoin_le ?_
    intro x hx
    rcases hx with rfl | hx
    · exact zero_mem (Algebra.adjoin R s)
    · exact Algebra.subset_adjoin hx
  · exact Algebra.adjoin_mono (Set.subset_insert 0 s)
