import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Injective f)

theorem comap_map_eq_of_injective (S : Submonoid M) : (S.map f).comap f = S := (Submonoid.gciMapComap hf).u_l_eq _

