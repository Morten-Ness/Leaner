import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem coe_mker (f : F) : (MonoidHom.mker f : Set M) = (f : M → N) ⁻¹' {1} := rfl

