import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem toSubsemiring_mono : Monotone (toSubsemiring : Subring R → Subsemiring R) := Subring.toSubsemiring_strictMono.monotone

