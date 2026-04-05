import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_le_iff_le : a.saturation ≤ b ↔ a ≤ b.toSubmonoid := Submonoid.gc_saturation ..

