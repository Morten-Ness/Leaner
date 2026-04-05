import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_center_iff {R : Type*} [Ring R] {z : R} : z ∈ Subring.center R ↔ ∀ g, g * z = z * g := Subsemigroup.mem_center_iff

