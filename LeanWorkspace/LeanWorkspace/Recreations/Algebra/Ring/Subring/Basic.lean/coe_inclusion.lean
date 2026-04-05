import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem coe_inclusion {S T : Subring R} (h : S ≤ T) (x : S) :
    (Subring.inclusion h x : R) = x := by simp [Subring.inclusion]

