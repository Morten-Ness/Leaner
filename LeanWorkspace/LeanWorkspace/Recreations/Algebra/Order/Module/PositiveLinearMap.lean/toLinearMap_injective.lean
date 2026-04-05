import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

theorem toLinearMap_injective : Function.Injective (toLinearMap : (E₁ →ₚ[R] E₂) → (E₁ →ₗ[R] E₂)) := fun _ _ h ↦ by PositiveLinearMap.ext x; congrm($h x)

