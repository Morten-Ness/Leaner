import Mathlib

open scoped RingTheory.LinearMap

variable {R A B : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

theorem comp_mul' (f : A →ₐ B) : f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) := TensorProduct.ext' <| by simp

