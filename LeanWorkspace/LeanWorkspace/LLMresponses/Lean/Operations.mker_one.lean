import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mker_one : MonoidHom.mker (1 : M →* N) = ⊤ := by
  ext x
  change (1 : M →* N) x = 1 ↔ x ∈ (⊤ : Submonoid M)
  simp only [Submonoid.mem_top, iff_true]
  rfl
