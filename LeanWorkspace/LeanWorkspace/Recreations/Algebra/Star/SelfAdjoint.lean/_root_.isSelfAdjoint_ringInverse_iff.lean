import Mathlib

variable {R A : Type*}

variable [NonAssocSemiring R] [StarRing R]

theorem _root_.isSelfAdjoint_ringInverse_iff {a : A} [Semiring A] [StarRing A] (ha : IsUnit a) :
    IsSelfAdjoint a⁻¹ʳ ↔ IsSelfAdjoint a := ⟨fun h => by grind [IsSelfAdjoint.ringInverse h], fun h => IsSelfAdjoint.ringInverse h⟩

