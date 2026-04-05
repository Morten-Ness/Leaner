import Mathlib

variable {R : Type u}

variable {R S : Type*} [CommRing R] [CommRing S]

theorem RingHom.ulift_apply (f : R →+* S) (x : ULift.{u₁} R) : f.ulift x = ⟨f x.down⟩ := rfl

