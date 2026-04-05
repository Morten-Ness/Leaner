import Mathlib

variable {M : Type*} [MulOneClass M]

theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (Submonoid.giSaturation M).l_top

