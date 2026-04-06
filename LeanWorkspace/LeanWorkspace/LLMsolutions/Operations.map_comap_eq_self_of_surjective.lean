import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_comap_eq_self_of_surjective {f : F} (h : Function.Surjective f) {S : Submonoid N} :
    Submonoid.map f (Submonoid.comap f S) = S := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases h y with ⟨x, rfl⟩
    exact ⟨x, hy, rfl⟩
