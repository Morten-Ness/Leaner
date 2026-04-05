import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendScalarsId_inv_app_apply (M : ModuleCat R) (m : M) :
    (ModuleCat.extendScalarsId R).inv.app M m = (1 : R) ⊗ₜ m := rfl

