import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem starClosure_le_iff {S₁ : Subalgebra R A} {S₂ : StarSubalgebra R A} :
    S₁.starClosure ≤ S₂ ↔ S₁ ≤ S₂.toSubalgebra := ⟨fun h => le_sup_left.trans h, Subalgebra.starClosure_le⟩

