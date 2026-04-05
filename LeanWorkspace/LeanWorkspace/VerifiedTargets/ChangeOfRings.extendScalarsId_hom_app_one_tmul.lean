import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem extendScalarsId_hom_app_one_tmul (M : ModuleCat R) (m : M) :
    (ModuleCat.extendScalarsId R).hom.app M ((1 : R) ⊗ₜ m) = m := by
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.homEquiv_extendScalarsId]
  dsimp

