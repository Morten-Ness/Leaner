import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S] (f : R →+* S)

set_option backward.inferInstanceAs.wrap.data false in
theorem smul_apply (M : ModuleCat R) (g : (ModuleCat.coextendScalars f).obj M) (s s' : S) :
    (s • g) s' = g (s' * s) := rfl

