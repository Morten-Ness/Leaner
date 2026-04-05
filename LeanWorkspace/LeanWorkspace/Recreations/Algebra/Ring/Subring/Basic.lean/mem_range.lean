import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (g : S →+* T) (f : R →+* S)

theorem mem_range {f : R →+* S} {y : S} : y ∈ f.range ↔ ∃ x, f x = y := Iff.rfl

