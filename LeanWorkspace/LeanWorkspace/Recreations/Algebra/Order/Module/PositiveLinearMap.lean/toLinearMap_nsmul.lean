import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

variable [IsOrderedAddMonoid E₂]

theorem toLinearMap_nsmul (f : E₁ →ₚ[R] E₂) (n : ℕ) :
    (n • f).toLinearMap = n • f.toLinearMap := rfl

