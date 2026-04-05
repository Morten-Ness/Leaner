import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem prod_mono_right (s : Subring R) : Monotone fun t : Subring S => s.prod t := Subring.prod_mono (le_refl s)

