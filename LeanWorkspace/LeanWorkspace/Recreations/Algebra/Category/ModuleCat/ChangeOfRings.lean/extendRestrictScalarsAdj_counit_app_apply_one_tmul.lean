import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem extendRestrictScalarsAdj_counit_app_apply_one_tmul (M : ModuleCat S) (m : M) :
    dsimp% (ModuleCat.extendRestrictScalarsAdj f).counit.app M ((1 : S) ⊗ₜ[R] m) = m := by
  apply ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul

