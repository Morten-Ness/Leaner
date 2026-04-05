import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B]

variable [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

theorem gc : GaloisConnection (NonUnitalStarAlgebra.adjoin R : Set A → NonUnitalStarSubalgebra R A) (↑) := by
  intro s S
  rw [← NonUnitalStarSubalgebra.toNonUnitalSubalgebra_le_iff, NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra,
    NonUnitalAlgebra.adjoin_le_iff, NonUnitalStarSubalgebra.coe_toNonUnitalSubalgebra]
  exact ⟨fun h => Set.subset_union_left.trans h,
    fun h => Set.union_subset h fun x hx => star_star x ▸ star_mem (show star x ∈ S from h hx)⟩

