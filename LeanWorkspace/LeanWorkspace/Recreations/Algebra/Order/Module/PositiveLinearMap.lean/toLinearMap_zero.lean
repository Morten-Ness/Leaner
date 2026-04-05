import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

theorem toLinearMap_zero : (0 : E₁ →ₚ[R] E₂).toLinearMap = 0 := rfl

