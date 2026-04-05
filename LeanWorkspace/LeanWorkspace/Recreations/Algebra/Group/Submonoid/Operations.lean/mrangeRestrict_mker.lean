import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrangeRestrict_mker (f : M →* N) : MonoidHom.mker (MonoidHom.mrangeRestrict f) = MonoidHom.mker f := by
  ext x
  change (⟨f x, _⟩ : MonoidHom.mrange f) = ⟨1, _⟩ ↔ f x = 1
  simp

