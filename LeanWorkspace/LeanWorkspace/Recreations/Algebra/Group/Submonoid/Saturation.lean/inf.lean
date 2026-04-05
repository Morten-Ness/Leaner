import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h₁ h₂ in
theorem inf : Submonoid.MulSaturated (s₁ ⊓ s₂) := fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

