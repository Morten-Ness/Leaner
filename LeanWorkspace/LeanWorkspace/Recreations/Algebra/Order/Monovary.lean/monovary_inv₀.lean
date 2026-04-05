import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem monovary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by
  rw [monovary_inv_left₀ hf, antivary_inv_right₀ hg]

