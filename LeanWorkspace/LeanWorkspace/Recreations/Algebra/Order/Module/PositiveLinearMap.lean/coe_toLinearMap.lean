import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

theorem coe_toLinearMap (f : E₁ →ₚ[R] E₂) : (f.toLinearMap : E₁ → E₂) = f := rfl

