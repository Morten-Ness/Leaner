import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendRestrictScalarsAdj_homEquiv_apply
    {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]
    {f : R →+* S} {M : ModuleCat.{max v u₂} R} {N : ModuleCat S}
    (φ : (ModuleCat.extendScalars f).obj M ⟶ N) (m : M) :
    (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ φ m = φ ((1 : S) ⊗ₜ m) := rfl

