import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mem_map_of_mem (f : F) {S : Submonoid M} {x : M} (hx : x ∈ S) : f x ∈ S.map f := mem_image_of_mem f hx

