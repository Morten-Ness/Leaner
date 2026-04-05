import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [StarModule R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem starClosure_le_iff {S₁ : NonUnitalSubalgebra R A} {S₂ : NonUnitalStarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toNonUnitalSubalgebra := ⟨fun h => le_sup_left.trans h, NonUnitalSubalgebra.starClosure_le⟩

