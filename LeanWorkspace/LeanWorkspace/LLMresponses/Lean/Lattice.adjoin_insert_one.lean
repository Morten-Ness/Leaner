FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_one (s : Set A) : Algebra.adjoin R (insert 1 s) = Algebra.adjoin R s := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    intro x hx
    rcases hx with rfl | hx
    · exact (Algebra.adjoin R s).one_mem
    · exact Algebra.subset_adjoin hx
  · refine Algebra.adjoin_le ?_
    intro x hx
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem hx)
