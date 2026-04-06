FAIL
import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := by
  intro x hx
  exact show x ∈ a.saturation by
    simp [Submonoid.saturation, hx]
