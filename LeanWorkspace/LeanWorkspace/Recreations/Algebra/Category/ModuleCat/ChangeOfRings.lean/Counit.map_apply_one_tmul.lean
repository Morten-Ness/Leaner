import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem Counit.map_apply_one_tmul {Y : ModuleCat S} (y : Y) :
    ModuleCat.ExtendRestrictScalarsAdj.Counit.map f ((1 : S) ⊗ₜ[R] y) = y := by
  change (1 : S) • y = y
  simp

