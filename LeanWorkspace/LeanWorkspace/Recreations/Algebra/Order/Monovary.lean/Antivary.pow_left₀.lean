import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem Antivary.pow_left₀ (hf : 0 ≤ f) (hfg : Antivary f g) (n : ℕ) : Antivary (f ^ n) g := fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _

