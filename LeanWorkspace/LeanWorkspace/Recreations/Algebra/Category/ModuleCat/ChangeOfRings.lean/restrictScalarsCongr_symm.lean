import Mathlib

theorem restrictScalarsCongr_symm
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g) :
  (ModuleCat.restrictScalarsCongr e).symm = ModuleCat.restrictScalarsCongr e.symm := rfl

