import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mk'_toAddSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toAddSubmonoid = sa := SetLike.coe_injective ha.symm

