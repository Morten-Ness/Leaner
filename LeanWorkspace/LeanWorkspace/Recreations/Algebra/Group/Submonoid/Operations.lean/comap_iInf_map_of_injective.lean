import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Injective f)

theorem comap_iInf_map_of_injective (S : ι → Submonoid M) : (⨅ i, (S i).map f).comap f = iInf S := (Submonoid.gciMapComap hf).u_iInf_l _

