import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mker_inl : MonoidHom.mker (inl M N) = ⊥ := by
  ext x
  simp [MonoidHom.mem_mker]

