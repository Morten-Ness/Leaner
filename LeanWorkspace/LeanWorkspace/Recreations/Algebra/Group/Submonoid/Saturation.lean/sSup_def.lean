import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

