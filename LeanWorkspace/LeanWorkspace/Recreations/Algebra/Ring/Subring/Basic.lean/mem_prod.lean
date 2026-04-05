import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_prod {s : Subring R} {t : Subring S} {p : R × S} : p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := Iff.rfl

