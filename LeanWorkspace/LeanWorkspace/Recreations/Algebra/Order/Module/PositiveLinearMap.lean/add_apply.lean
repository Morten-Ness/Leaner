import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

variable [IsOrderedAddMonoid E₂]

theorem add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl

