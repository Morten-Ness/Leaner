import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_id (S : Submonoid P) : S.comap (MonoidHom.id P) = S := ext (by simp)

