import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem coe_bot : ((⊥ : Subring R) : Set R) = Set.range ((↑) : ℤ → R) := RingHom.coe_range (Int.castRingHom R)

