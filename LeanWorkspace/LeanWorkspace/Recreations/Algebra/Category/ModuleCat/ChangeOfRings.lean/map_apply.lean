import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

theorem map_apply {M M' : ModuleCat R} (g : M ⟶ M') (x) (s : S) :
    (ModuleCat.coextendScalars f).map g x s = g (x s) := rfl

