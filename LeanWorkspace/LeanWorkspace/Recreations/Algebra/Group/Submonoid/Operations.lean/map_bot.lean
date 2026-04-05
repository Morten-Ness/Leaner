import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_bot (f : F) : (⊥ : Submonoid M).map f = ⊥ := (Submonoid.gc_map_comap f).l_bot

