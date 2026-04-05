import Mathlib

variable {M : Type*} [MulOneClass M]

theorem ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ := SetLike.ext h

