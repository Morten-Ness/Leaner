import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem toSubalgebra_le_iff {S₁ S₂ : StarSubalgebra R A} :
    S₁.toSubalgebra ≤ S₂.toSubalgebra ↔ S₁ ≤ S₂ := Iff.rfl

