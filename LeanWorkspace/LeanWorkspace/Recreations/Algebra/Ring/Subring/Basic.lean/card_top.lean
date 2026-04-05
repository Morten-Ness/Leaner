import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (s : Subring R)

theorem card_top (R) [NonAssocRing R] [Fintype R] : Fintype.card (⊤ : Subring R) = Fintype.card R := Fintype.card_congr Subring.topEquiv.toEquiv

