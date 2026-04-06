FAIL
import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h₁ h₂ in
theorem inf : Submonoid.MulSaturated (s₁ ⊓ s₂) := by
  intro x y hxy
  exact fun hs => ⟨h₁ hs, h₂ hs⟩
