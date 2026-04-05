import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (Submonoid.gc_saturation M).le_u_l a

