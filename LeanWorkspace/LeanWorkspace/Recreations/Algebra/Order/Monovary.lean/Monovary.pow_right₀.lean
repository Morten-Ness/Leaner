import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι → α} {g g₁ g₂ : ι → β}

theorem Monovary.pow_right₀ (hg : 0 ≤ g) (hfg : Monovary f g) (n : ℕ) : Monovary f (g ^ n) := (hfg.symm.pow_left₀ hg _).symm

