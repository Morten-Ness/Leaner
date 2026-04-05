import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrangeRestrict_surjective (f : M →* N) : Function.Surjective f.mrangeRestrict := fun ⟨_, ⟨x, rfl⟩⟩ => ⟨x, rfl⟩

