import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {ι : Type*} {f : F}

variable (hf : Function.Surjective f)

theorem map_iSup_comap_of_surjective (S : ι → Submonoid N) : (⨆ i, (S i).comap f).map f = iSup S := (Submonoid.giMapComap hf).l_iSup_u _

