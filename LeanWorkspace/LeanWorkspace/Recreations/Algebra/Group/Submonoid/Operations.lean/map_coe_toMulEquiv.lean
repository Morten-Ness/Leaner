import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_coe_toMulEquiv {F} [EquivLike F M N] [MulEquivClass F M N] (f : F) (S : Submonoid M) :
    S.map (f : M ≃* N) = S.map f := rfl

