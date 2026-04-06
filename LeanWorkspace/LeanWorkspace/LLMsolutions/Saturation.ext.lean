import Mathlib

variable {M : Type*} [MulOneClass M]

theorem ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ := by
  cases s₁
  cases s₂
  cases h
  rfl
