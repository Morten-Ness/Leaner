import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    StarAlgebra.adjoin R s ≤ StarSubalgebra.centralizer R (StarSubalgebra.centralizer R s) := by
  rw [← StarSubalgebra.toSubalgebra_le_iff, StarSubalgebra.centralizer_toSubalgebra, StarAlgebra.adjoin_toSubalgebra]
  convert Algebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp

