import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem εIso_inv_freeMk (x : PUnit) : (ModuleCat.FreeMonoidal.εIso R).inv (ModuleCat.freeMk x) = 1 := by
  dsimp [ModuleCat.FreeMonoidal.εIso, ModuleCat.freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

