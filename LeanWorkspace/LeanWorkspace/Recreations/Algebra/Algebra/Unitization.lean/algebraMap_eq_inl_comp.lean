import Mathlib

variable (S R A : Type*) [CommSemiring S] [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Algebra S R] [DistribMulAction S A]
  [IsScalarTower S R A]

theorem algebraMap_eq_inl_comp : ⇑(algebraMap S (Unitization R A)) = Unitization.inl ∘ algebraMap S R := rfl

