import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Surjective f)

theorem map_comap_eq_of_surjective (S : Submonoid N) : (S.comap f).map f = S := (Submonoid.giMapComap hf).l_u_eq _

