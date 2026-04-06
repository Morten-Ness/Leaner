import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem monotone_map {f : F} : Monotone (Submonoid.map f) := by
  intro A B hAB
  show Submonoid.map f A ≤ Submonoid.map f B
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hAB hx, rfl⟩
