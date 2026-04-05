import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem top : Submonoid.MulSaturated (⊤ : Submonoid M) := fun _ _ _ ↦ ⟨trivial, trivial⟩

