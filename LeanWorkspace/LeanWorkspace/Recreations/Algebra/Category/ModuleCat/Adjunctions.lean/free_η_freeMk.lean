import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem free_η_freeMk (x : PUnit) : η (ModuleCat.free R) (ModuleCat.freeMk x) = 1 := by
  apply FreeMonoidal.εIso_inv_freeMk

