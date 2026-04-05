import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem monotone_comap {f : F} : Monotone (Submonoid.comap f) := (Submonoid.gc_map_comap f).monotone_u

