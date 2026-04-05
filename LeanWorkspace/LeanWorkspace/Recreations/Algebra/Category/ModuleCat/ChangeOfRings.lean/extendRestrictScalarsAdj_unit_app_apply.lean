import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendRestrictScalarsAdj_unit_app_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{max v u₂} R) (m : M) :
    (ModuleCat.extendRestrictScalarsAdj f).unit.app M m = (1 : S) ⊗ₜ[R,f] m := rfl

