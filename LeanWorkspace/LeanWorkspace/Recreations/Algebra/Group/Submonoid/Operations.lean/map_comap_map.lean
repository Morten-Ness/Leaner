import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f := (Submonoid.gc_map_comap f).l_u_l_eq_l _

