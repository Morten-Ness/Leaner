import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f := (Submonoid.gc_map_comap f).u_l_u_eq_u _

