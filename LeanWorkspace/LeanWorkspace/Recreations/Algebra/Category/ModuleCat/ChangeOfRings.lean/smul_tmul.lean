import Mathlib

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
theorem smul_tmul {M : ModuleCat.{v} R} (s s' : S) (m : M) :
    s • (s' ⊗ₜ[R,f] m : (ModuleCat.extendScalars f).obj M) = (s * s') ⊗ₜ[R,f] m := rfl

