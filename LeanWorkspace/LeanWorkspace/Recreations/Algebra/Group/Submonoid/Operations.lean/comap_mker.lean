import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_mker (g : N →* P) (f : M →* N) : (MonoidHom.mker g).comap f = MonoidHom.mker (comp g f) := rfl

