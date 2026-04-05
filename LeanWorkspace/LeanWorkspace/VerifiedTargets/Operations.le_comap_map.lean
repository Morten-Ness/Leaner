import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem le_comap_map {f : F} : S ≤ (S.map f).comap f := (Submonoid.gc_map_comap f).le_u_l _

