import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem εIso_hom_one : (ModuleCat.FreeMonoidal.εIso R).hom 1 = ModuleCat.freeMk PUnit.unit := rfl

