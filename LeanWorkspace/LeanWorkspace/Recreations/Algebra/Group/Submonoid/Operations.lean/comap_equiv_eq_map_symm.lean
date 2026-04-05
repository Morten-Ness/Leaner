import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Submonoid M) :
    K.comap f = K.map f.symm := (Submonoid.map_equiv_eq_comap_symm f.symm K).symm

