import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem rangeS_subtype (s : Subsemiring R) : s.subtype.rangeS = s := SetLike.coe_injective <| (coe_rangeS _).trans Subtype.range_coe

