import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem range_fst : (fst R S).rangeS = ⊤ := (fst R S).rangeS_top_of_surjective <| Prod.fst_surjective

