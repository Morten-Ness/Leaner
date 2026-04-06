FAIL
import Mathlib

variable {M : Type*}

variable [MulOneClass M]

theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation := by
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro i
    exact le_iSup (fun j => (f j).toSubmonoid) i
  · refine saturation_le.2 ?_
    refine iSup_le ?_
    intro i
    exact (show (f i).toSubmonoid ≤ (iSup f).toSubmonoid from le_iSup f i)
