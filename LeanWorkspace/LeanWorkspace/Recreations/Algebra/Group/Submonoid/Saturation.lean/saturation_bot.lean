import Mathlib

variable {M : Type*} [MulOneClass M]

theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (Submonoid.gc_saturation M).l_bot

