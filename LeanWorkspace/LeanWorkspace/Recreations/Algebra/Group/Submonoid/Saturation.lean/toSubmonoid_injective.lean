import Mathlib

variable {M : Type*} [MulOneClass M]

theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq ↦ by congr

