import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable (M : ModuleCat.{v} R)

set_option backward.isDefEq.respectTransparency false in
theorem map'_id {M : ModuleCat.{v} R} : ModuleCat.ExtendScalars.map' f (𝟙 M) = 𝟙 _ := by
  simp [ModuleCat.ExtendScalars.map', ModuleCat.ExtendScalars.obj']

