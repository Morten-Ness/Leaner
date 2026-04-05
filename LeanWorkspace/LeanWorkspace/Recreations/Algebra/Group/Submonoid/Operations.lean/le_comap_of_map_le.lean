import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem le_comap_of_map_le {T : Submonoid N} {f : F} : S.map f ≤ T → S ≤ T.comap f := (Submonoid.gc_map_comap f).le_u

