import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι → α} {g g₁ g₂ : ι → β}

theorem MonovaryOn.mul_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 ≤ g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : MonovaryOn f (g₁ * g₂) s := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm

