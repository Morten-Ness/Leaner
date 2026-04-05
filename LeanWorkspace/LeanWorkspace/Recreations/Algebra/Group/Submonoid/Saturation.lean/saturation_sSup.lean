import Mathlib

variable {M : Type*} [MulOneClass M]

theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s ∈ f, s.saturation := (Submonoid.gc_saturation M).l_sSup

