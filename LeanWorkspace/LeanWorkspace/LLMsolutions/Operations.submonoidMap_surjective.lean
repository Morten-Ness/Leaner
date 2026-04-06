import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem submonoidMap_surjective (f : M →* N) (M' : Submonoid M) :
    Function.Surjective (f.submonoidMap M') := by
  intro x
  rcases x.2 with ⟨y, hy, hfy⟩
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  exact hfy
