import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem restrict_mrange (f : M →* N) : MonoidHom.mrange (f.restrict S) = S.map f := by
  simp [SetLike.ext_iff]

