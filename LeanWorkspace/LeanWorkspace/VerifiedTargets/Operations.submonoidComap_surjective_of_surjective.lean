import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem submonoidComap_surjective_of_surjective (f : M →* N) (N' : Submonoid N) (hf : Function.Surjective f) :
    Function.Surjective (f.submonoidComap N') := fun y ↦ by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submonoid.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

