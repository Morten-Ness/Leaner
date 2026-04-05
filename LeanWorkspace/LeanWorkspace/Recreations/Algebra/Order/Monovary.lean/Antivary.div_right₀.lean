import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem Antivary.div_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
    (h₂ : Monovary f g₂) : Antivary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

