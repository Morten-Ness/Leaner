import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_eq_top {f : F} : MonoidHom.mrange f = (⊤ : Submonoid N) ↔ Function.Surjective f := SetLike.ext'_iff.trans <| Iff.trans (by rw [MonoidHom.coe_mrange, coe_top]) Set.range_eq_univ

