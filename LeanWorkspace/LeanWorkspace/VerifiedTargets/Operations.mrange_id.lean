import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_id : MonoidHom.mrange (MonoidHom.id M) = ⊤ := by
  simp [MonoidHom.mrange_eq_map]

