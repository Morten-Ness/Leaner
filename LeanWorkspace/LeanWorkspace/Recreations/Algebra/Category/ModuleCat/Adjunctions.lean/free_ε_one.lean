import Mathlib

variable (R : Type u)

variable [CommRing R]

theorem free_ε_one : ε (ModuleCat.free R) 1 = ModuleCat.freeMk PUnit.unit := rfl

