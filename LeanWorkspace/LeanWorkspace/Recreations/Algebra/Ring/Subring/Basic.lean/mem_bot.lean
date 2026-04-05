import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_bot {x : R} : x ∈ (⊥ : Subring R) ↔ ∃ n : ℤ, ↑n = x := RingHom.mem_range

