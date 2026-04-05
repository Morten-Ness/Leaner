import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem coe_map (f : R →+* S) (s : Subring R) : (s.map f : Set S) = f '' s := rfl

