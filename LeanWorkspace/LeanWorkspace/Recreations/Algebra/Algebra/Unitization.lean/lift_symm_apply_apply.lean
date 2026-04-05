import Mathlib

variable {S R A : Type*} [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] {B : Type*} [Semiring B] [Algebra S B] [Algebra S R]
  [DistribMulAction S A] [IsScalarTower S R A] {C : Type*} [Semiring C] [Algebra R C]

theorem lift_symm_apply_apply (φ : Unitization R A →ₐ[R] C) (a : A) :
    Unitization.lift.symm φ a = φ a := rfl

