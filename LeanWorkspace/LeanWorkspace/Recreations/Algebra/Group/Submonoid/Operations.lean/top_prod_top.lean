import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem top_prod_top : (⊤ : Submonoid M).prod (⊤ : Submonoid N) = ⊤ := (Submonoid.top_prod _).trans <| Submonoid.comap_top _

