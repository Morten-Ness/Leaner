import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem apply_coe_mem_map (f : F) (S : Submonoid M) (x : S) : f x ∈ S.map f := Submonoid.mem_map_of_mem f x.2

