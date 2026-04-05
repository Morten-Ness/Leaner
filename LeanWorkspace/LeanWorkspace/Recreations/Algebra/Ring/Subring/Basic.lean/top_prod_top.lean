import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem top_prod_top : (⊤ : Subring R).prod (⊤ : Subring S) = ⊤ := (Subring.top_prod _).trans <| Subring.comap_top _

