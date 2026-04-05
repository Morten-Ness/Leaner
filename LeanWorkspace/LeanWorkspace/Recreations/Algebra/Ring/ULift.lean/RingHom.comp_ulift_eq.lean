import Mathlib

variable {R : Type u}

variable {R S : Type*} [CommRing R] [CommRing S]

theorem RingHom.comp_ulift_eq (f : R →+* S) :
    ULift.ringEquiv.toRingHom.comp ((ulift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = f := rfl

