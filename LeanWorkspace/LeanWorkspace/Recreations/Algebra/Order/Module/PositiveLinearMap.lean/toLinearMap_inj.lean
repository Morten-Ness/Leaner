import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

theorem toLinearMap_inj {f g : E₁ →ₚ[R] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g := PositiveLinearMap.toLinearMap_injective.eq_iff

