import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s t : Subring R}

theorem toSubmonoid_strictMono : StrictMono (fun s : Subring R => s.toSubmonoid) := fun _ _ => id

