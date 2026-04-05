import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_eq_top_of_surjective (f : F) (hf : Function.Surjective f) :
    MonoidHom.mrange f = (⊤ : Submonoid N) := MonoidHom.mrange_eq_top.2 hf

