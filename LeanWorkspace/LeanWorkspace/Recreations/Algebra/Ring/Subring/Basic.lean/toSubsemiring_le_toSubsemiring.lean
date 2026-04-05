import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem toSubsemiring_le_toSubsemiring (hst : s ≤ t) : s.toSubsemiring ≤ t.toSubsemiring := hst

