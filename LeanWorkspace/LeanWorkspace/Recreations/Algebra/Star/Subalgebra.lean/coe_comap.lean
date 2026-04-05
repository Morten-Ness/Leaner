import Mathlib

variable {F R A B C : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

variable [Semiring B] [StarRing B] [Algebra R B] [StarModule R B]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

variable (S : StarSubalgebra R A)

theorem coe_comap (S : StarSubalgebra R B) (f : A →⋆ₐ[R] B) :
    (S.comap f : Set A) = f ⁻¹' (S : Set B) := rfl

