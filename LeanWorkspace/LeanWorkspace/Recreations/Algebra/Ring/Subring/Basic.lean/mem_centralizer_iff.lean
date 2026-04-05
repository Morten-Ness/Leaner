import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_centralizer_iff {R} [Ring R] {s : Set R} {z : R} :
    z ∈ Subring.centralizer s ↔ ∀ g ∈ s, g * z = z * g := Iff.rfl

