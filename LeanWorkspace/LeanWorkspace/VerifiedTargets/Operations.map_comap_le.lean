import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_le {S : Submonoid N} {f : F} : (S.comap f).map f ≤ S := (Submonoid.gc_map_comap f).l_u_le _

