import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mem_map {f : F} {S : Submonoid M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := Iff.rfl

