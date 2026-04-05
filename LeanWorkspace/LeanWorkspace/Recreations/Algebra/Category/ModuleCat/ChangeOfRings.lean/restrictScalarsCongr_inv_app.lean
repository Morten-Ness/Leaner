import Mathlib

theorem restrictScalarsCongr_inv_app
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] {f g : R →+* S} (e : f = g)
    (M : ModuleCat S) (x : M) :
  (ModuleCat.restrictScalarsCongr e).inv.app M x = x := rfl

