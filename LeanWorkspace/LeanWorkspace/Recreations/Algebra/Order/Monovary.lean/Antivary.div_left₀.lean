import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem Antivary.div_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
    (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g := fun _i _j hij ↦ div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) <| h₂ hij

