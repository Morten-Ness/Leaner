FAIL
import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  constructor
  · intro hx
    simpa using hx
  · intro hx
    simpa using hx
