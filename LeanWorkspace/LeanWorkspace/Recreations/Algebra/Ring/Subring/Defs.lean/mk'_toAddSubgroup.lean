import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mk'_toAddSubgroup {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toAddSubgroup = sa := SetLike.coe_injective ha.symm

