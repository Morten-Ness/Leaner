import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_mrange (g : N →* P) (f : M →* N) : (MonoidHom.mrange f).map g = MonoidHom.mrange (comp g f) := by
  simpa only [MonoidHom.mrange_eq_map] using Submonoid.map_map (⊤ : Submonoid M) g f

