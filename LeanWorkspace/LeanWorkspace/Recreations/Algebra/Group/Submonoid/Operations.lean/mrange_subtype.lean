import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_subtype (s : Submonoid M) : MonoidHom.mrange s.subtype = s := SetLike.coe_injective <| (MonoidHom.coe_mrange _).trans <| Subtype.range_coe

