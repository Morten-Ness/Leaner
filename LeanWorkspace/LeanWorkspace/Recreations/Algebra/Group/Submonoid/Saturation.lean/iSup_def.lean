import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation := (Submonoid.giSaturation M).l_iSup_u f |>.symm

