import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem algHom_ext ⦃φ₁ φ₂ : R[M] →ₐ[R] A⦄ (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ := AlgHom.toLinearMap_injective <| lhom_ext' fun a ↦ LinearMap.ext_ring (h a)

-- The priority must be `high`.

