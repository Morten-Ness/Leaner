FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommRing R] [Ring A]

variable [Algebra R A] {s t : Set A}

theorem adjoin_insert_intCast (n : ℤ) (s : Set A) : Algebra.adjoin R (insert (n : A) s) = Algebra.adjoin R s := by
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    intro x hx
    rcases hx with rfl | hx
    · change (n : A) ∈ Algebra.adjoin R s
      exact Subsemiring.intCast_mem (Algebra.adjoin R s) n
    · exact Algebra.subset_adjoin hx
  · exact Algebra.adjoin_mono (Set.subset_insert _ _)
