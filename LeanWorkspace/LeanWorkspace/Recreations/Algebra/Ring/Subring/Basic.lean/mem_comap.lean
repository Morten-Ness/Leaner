import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem mem_comap {s : Subring S} {f : R →+* S} {x : R} : x ∈ s.comap f ↔ f x ∈ s := Iff.rfl

