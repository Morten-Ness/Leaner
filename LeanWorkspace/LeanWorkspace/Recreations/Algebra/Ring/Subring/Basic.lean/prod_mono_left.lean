import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem prod_mono_left (t : Subring S) : Monotone fun s : Subring R => s.prod t := fun _ _ hs =>
  Subring.prod_mono hs (le_refl t)

