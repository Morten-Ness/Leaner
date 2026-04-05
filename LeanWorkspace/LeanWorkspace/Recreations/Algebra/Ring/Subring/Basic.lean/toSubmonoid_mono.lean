import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem toSubmonoid_mono : Monotone (fun s : Subring R => s.toSubmonoid) := Subring.toSubmonoid_strictMono.monotone

