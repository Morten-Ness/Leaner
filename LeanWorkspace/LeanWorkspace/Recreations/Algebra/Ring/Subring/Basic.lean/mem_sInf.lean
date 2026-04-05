import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem mem_sInf {S : Set (Subring R)} {x : R} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := Set.mem_iInter₂

