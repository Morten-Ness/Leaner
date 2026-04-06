FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B]
variable [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_union (s t : Set A) :
    Algebra.adjoin R (s ∪ t) = Algebra.adjoin R s ⊔ Algebra.adjoin R t := by
  ext x
  constructor
  · intro hx
    refine Algebra.adjoin_le ?_ hx
    intro y hy
    rcases hy with hy | hy
    · exact le_sup_of_le_left (Algebra.subset_adjoin hy)
    · exact le_sup_of_le_right (Algebra.subset_adjoin hy)
  · intro hx
    exact sup_le
      (Algebra.adjoin_le <| by
        intro y hy
        exact Algebra.subset_adjoin (Or.inl hy))
      (Algebra.adjoin_le <| by
        intro y hy
        exact Algebra.subset_adjoin (Or.inr hy))
      hx
