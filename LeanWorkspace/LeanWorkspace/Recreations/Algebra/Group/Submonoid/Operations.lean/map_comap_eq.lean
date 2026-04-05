import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq (f : F) (S : Submonoid N) : (S.comap f).map f = S ⊓ MonoidHom.mrange f := SetLike.coe_injective Set.image_preimage_eq_inter_range

