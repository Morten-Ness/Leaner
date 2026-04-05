import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_top (f : F) : (⊤ : Submonoid N).comap f = ⊤ := (Submonoid.gc_map_comap f).u_top

