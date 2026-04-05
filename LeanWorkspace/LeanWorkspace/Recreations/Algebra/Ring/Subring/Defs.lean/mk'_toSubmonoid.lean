import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mk'_toSubmonoid {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R}
    (ha : ↑sa = s) : (Subring.mk' s sm sa hm ha).toSubmonoid = sm := SetLike.coe_injective hm.symm

