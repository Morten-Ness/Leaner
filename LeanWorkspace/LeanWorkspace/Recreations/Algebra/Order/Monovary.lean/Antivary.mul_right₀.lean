import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι → α} {g g₁ g₂ : ι → β}

theorem Antivary.mul_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

