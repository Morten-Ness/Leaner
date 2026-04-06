FAIL
import Mathlib

variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]

variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

variable [Semiring C] [Algebra R C] [StarRing C]

theorem starAlgHom_ext {φ ψ : Unitization R A →⋆ₐ[R] C}
    (h : (φ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A) =
      (ψ : Unitization R A →⋆ₙₐ[R] C).comp (Unitization.inrNonUnitalStarAlgHom R A)) :
    φ = ψ := by
  ext r
  · simp
  · exact congrFun h r
