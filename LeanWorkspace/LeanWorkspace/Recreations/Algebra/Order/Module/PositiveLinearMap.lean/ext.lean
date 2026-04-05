import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

theorem ext {f g : E₁ →ₚ[R] E₂} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

