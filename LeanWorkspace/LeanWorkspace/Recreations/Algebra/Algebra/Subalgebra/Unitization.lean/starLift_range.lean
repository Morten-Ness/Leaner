import Mathlib

variable {R A C : Type*} [CommSemiring R] [NonUnitalSemiring A] [StarRing R] [StarRing A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarModule R A]

variable [Semiring C] [StarRing C] [Algebra R C] [StarModule R C]

theorem starLift_range (f : A →⋆ₙₐ[R] C) :
    (starLift f).range = StarAlgebra.adjoin R (NonUnitalStarAlgHom.range f : Set C) := eq_of_forall_ge_iff fun c ↦ by
    rw [Unitization.starLift_range_le, StarAlgebra.adjoin_le_iff]
    rfl

