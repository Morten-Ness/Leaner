import Mathlib

variable {R A B C : Type*} [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [NonUnitalSemiring B] [StarRing B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

variable [NonUnitalSemiring C] [StarRing C] [Module R C] [SMulCommClass R C C] [IsScalarTower R C C]

variable [StarModule R B] [StarModule R C]

theorem starMap_comp {φ : A →⋆ₙₐ[R] B} {ψ : B →⋆ₙₐ[R] C} :
    Unitization.starMap (ψ.comp φ) = (Unitization.starMap ψ).comp (Unitization.starMap φ) := by
  ext; all_goals simp

