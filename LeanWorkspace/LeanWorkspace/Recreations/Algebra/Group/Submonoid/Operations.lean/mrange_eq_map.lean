import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_eq_map (f : F) : MonoidHom.mrange f = (⊤ : Submonoid M).map f := Submonoid.copy_eq _

