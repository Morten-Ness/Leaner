import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mem_comap {S : Submonoid N} {f : F} {x : M} : x ∈ S.comap f ↔ f x ∈ S := Iff.rfl

