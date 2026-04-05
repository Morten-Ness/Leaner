import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_le_of_le_comap {T : Submonoid N} {f : F} : S ≤ T.comap f → S.map f ≤ T := (Submonoid.gc_map_comap f).l_le

