import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq_self {f : F} {S : Submonoid N} (h : S ≤ MonoidHom.mrange f) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using Submonoid.map_comap_eq f S

