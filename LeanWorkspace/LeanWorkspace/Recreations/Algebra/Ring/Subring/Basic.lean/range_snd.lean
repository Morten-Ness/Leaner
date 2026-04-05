import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem range_snd : (snd R S).rangeS = ⊤ := (snd R S).rangeS_top_of_surjective <| Prod.snd_surjective

