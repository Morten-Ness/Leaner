import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_tmul {M M' : ModuleCat.{v} R} (g : M ⟶ M') (s : S) (m : M) :
    (ModuleCat.extendScalars f).map g (s ⊗ₜ[R,f] m) = s ⊗ₜ[R,f] g m := rfl

