import Mathlib

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂]

variable [IsOrderedAddMonoid E₂]

theorem nsmul_apply (f : E₁ →ₚ[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) := rfl

