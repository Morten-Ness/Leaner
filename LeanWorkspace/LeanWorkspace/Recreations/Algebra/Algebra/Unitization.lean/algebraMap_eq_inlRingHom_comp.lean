import Mathlib

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

theorem algebraMap_eq_inlRingHom_comp :
    algebraMap S (Unitization R A) = (Unitization.inlRingHom R A).comp (algebraMap S R) := rfl

