import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_iSup {ι : Sort*} (f : F) (s : ι → Submonoid M) : (iSup s).map f = ⨆ i, (s i).map f := (Submonoid.gc_map_comap f : GaloisConnection (Submonoid.map f) (Submonoid.comap f)).l_iSup

