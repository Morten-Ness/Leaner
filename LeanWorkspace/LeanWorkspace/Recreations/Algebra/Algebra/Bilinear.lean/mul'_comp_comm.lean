import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

theorem mul'_comp_comm : LinearMap.mul' R A ∘ₗ TensorProduct.comm R A A = LinearMap.mul' R A := by
  simp [LinearMap.mul', lift_comp_comm_eq]

