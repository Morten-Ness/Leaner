import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_map {f : F} : ((S.map f).comap f).map f = S.map f := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    exact ⟨x, hx, rfl⟩
