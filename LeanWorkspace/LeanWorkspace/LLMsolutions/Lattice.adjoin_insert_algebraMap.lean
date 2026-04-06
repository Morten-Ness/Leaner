FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_algebraMap (x : R) (s : Set A) :
    Algebra.adjoin R (insert (algebraMap R A x) s) = Algebra.adjoin R s := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact Algebra.subset_adjoin hy
    · exact Algebra.subset_adjoin hy
  · exact Algebra.adjoin_mono (Set.subset_insert _ _)
