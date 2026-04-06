import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_id : MonoidHom.mrange (MonoidHom.id M) = ⊤ := by
  ext x
  constructor
  · intro hx
    trivial
  · intro hx
    rcases hx with _
    exact ⟨x, rfl⟩
