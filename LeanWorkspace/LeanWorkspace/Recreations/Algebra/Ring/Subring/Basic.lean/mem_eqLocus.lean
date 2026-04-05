import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

variable {S : Type v} [Semiring S]

theorem mem_eqLocus {f g : R →+* S} {x : R} : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

