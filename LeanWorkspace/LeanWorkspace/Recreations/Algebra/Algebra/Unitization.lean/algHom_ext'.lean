import Mathlib

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem algHom_ext' {φ ψ : Unitization R A →ₐ[R] C}
    (h :
      φ.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom R A) =
        ψ.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom R A)) :
    φ = ψ := Unitization.algHom_ext'' (NonUnitalAlgHom.congr_fun h)

