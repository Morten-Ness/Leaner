import Mathlib

open scoped RingTheory.LinearMap

variable {R A B : Type*}

variable [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonUnitalNonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]

theorem comp_mul' (f : A →ₙₐ[R] B) : (f : A →ₗ[R] B) ∘ₗ μ = μ[R] ∘ₗ (f ⊗ₘ f) := TensorProduct.ext' <| by simp

