import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem coe_comap (S : Submonoid N) (f : F) : (S.comap f : Set M) = f ⁻¹' S := rfl

