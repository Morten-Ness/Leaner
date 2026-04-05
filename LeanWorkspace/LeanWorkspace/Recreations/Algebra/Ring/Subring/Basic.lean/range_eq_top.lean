import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Subring R}

theorem range_eq_top {f : R →+* S} :
    f.range = (⊤ : Subring S) ↔ Function.Surjective f := SetLike.ext'_iff.trans <| Iff.trans (by rw [RingHom.coe_range, Subring.coe_top]) Set.range_eq_univ

