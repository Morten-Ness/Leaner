import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem restrict_mker (f : M →* N) : MonoidHom.mker (f.restrict S) = (MonoidHom.mker f).comap S.subtype := rfl

