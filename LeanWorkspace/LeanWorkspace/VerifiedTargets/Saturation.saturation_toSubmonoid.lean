import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_toSubmonoid : b.saturation = b := (Submonoid.giSaturation M).l_u_eq b

