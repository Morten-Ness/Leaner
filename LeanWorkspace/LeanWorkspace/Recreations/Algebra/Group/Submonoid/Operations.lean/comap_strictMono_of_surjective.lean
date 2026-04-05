import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Surjective f)

theorem comap_strictMono_of_surjective : StrictMono (Submonoid.comap f) := (Submonoid.giMapComap hf).strictMono_u

