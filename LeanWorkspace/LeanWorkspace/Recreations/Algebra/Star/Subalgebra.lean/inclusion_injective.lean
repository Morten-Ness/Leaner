import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem inclusion_injective {S₁ S₂ : StarSubalgebra R A} (h : S₁ ≤ S₂) :
    Function.Injective <| StarSubalgebra.inclusion h := Set.inclusion_injective h

