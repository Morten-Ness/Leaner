import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem homEquiv_extendScalarsId (M : ModuleCat R) :
    (ModuleCat.extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _ ((ModuleCat.extendScalarsId R).hom.app M) =
      (restrictScalarsId R).inv.app M := by
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ← ModuleCat.extendScalarsId_inv_app_apply, ← comp_apply]
  simp

