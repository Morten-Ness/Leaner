import Mathlib

variable {R A B : Type*}

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

variable {M : Type*} [AddCommMonoid M] [Module R M]

theorem lift_lsmul_mul_eq_lsmul_lift_lsmul {r : R} :
    lift (lsmul R M ∘ₗ LinearMap.mul R R r) = lsmul R M r ∘ₗ lift (lsmul R M) := by
  apply TensorProduct.ext'
  intro x a
  simp [← mul_smul, mul_comm]

