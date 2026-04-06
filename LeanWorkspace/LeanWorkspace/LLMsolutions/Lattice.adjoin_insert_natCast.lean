FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_insert_natCast (n : ℕ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := by
  refine le_antisymm ?_ (Algebra.adjoin_mono (Set.subset_insert _ _))
  refine Algebra.adjoin_le ?_
  intro x hx
  rcases hx with rfl | hx
  · change algebraMap R A (n : R) ∈ Algebra.adjoin R s
    exact SetLike.algebraMap_mem _ (n : R)
  · exact Algebra.subset_adjoin hx
