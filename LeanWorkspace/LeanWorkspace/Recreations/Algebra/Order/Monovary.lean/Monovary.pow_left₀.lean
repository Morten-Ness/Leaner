import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem Monovary.pow_left₀ (hf : 0 ≤ f) (hfg : Monovary f g) (n : ℕ) : Monovary (f ^ n) g := fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _

