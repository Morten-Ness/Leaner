import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : Submonoid N} :
    Submonoid.map f (Submonoid.comap f S) = S := Submonoid.map_comap_eq_self (MonoidHom.mrange_eq_top_of_surjective _ h ▸ le_top)

