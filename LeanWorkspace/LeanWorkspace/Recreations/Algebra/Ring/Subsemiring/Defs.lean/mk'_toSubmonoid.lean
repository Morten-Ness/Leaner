import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R}
    (ha : ↑sa = s) : (Subsemiring.mk' s sm hm sa ha).toSubmonoid = sm := SetLike.coe_injective hm.symm

