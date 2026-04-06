import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem map_equiv_top (f : M ≃* N) : (⊤ : Submonoid M).map f = ⊤ := by
  ext x
  simp [Submonoid.mem_map]
