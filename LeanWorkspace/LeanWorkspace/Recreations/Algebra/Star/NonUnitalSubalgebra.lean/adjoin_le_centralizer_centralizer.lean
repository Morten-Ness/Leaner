import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    NonUnitalStarAlgebra.adjoin R s ≤ NonUnitalStarSubalgebra.centralizer R (NonUnitalStarSubalgebra.centralizer R s) := by
  rw [← NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff, NonUnitalStarSubalgebra.centralizer_toNonUnitalSubalgebra,
    NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra]
  convert NonUnitalAlgebra.adjoin_le_centralizer_centralizer R (s ∪ star s)
  rw [StarMemClass.star_coe_eq]
  simp

