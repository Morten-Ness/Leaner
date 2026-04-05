import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem coe_comap (s : Subring S) (f : R →+* S) : (s.comap f : Set R) = f ⁻¹' s := rfl

