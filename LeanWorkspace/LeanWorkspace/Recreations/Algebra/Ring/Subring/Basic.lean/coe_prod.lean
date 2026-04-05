import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem coe_prod (s : Subring R) (t : Subring S) :
    (s.prod t : Set (R × S)) = (s : Set R) ×ˢ (t : Set S) := rfl

