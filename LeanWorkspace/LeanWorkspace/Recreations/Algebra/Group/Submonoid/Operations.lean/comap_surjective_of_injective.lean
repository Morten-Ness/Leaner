import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Injective f)

theorem comap_surjective_of_injective : Function.Surjective (Submonoid.comap f) := (Submonoid.gciMapComap hf).u_surjective

