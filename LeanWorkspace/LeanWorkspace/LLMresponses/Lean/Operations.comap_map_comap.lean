import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem comap_map_comap {S : Submonoid N} {f : F} : ((S.comap f).map f).comap f = S.comap f := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hxy⟩
    simpa [hxy] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩
