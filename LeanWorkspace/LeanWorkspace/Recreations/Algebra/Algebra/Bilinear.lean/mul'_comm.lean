import Mathlib

variable {R A B : Type*}

variable [CommSemiring R] [NonUnitalCommSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

theorem mul'_comm (x : A ⊗[R] A) : LinearMap.mul' R A (TensorProduct.comm R A A x) = LinearMap.mul' R A x := congr($LinearMap.mul'_comp_comm _)

