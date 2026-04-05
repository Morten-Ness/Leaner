import Mathlib

variable {R : Type u}

variable {R S : Type*} [CommRing R] [CommRing S]

theorem RingHom.down_ulift_apply (f : R →+* S) (x : ULift.{u₁} R) :
    (f.ulift x).down = f x.down := rfl

