import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Submonoid M) :
    K.map f = K.comap f.symm := SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

