import Mathlib

variable {M : Type*} [MulOneClass M]

theorem saturation_iSup {ι : Sort*} {f : ι → Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (Submonoid.gc_saturation M).l_iSup

