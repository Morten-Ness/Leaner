import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem star_adjoin_comm (s : Set A) : star (Algebra.adjoin R s) = Algebra.adjoin R (star s) := have this : ∀ t : Set A, Algebra.adjoin R (star t) ≤ star (Algebra.adjoin R t) := fun _ =>
    Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
  le_antisymm (by simpa only [star_star] using Subalgebra.star_mono (this (star s))) (this s)

