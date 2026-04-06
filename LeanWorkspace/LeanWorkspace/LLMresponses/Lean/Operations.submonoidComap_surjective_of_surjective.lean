import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem submonoidComap_surjective_of_surjective (f : M →* N) (N' : Submonoid N) (hf : Function.Surjective f) :
    Function.Surjective (f.submonoidComap N') := by
  intro x
  rcases hf x.1 with ⟨y, hy⟩
  refine ⟨⟨y, by simpa [hy] using x.2⟩, ?_⟩
  ext
  exact hy
