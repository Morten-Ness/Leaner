import Mathlib

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [Semiring C] [Algebra R C] [StarRing C]

variable [StarModule R C]

theorem starLift_symm_apply_apply (φ : Unitization R A →⋆ₐ[R] C) (a : A) :
    Unitization.starLift.symm φ a = φ a := rfl

