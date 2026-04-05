import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem antivary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by
  rw [antivary_inv_left₀ hf, monovary_inv_right₀ hg]

