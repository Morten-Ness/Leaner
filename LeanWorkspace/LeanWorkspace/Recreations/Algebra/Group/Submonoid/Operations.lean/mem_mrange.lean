import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mem_mrange {f : F} {y : N} : y ∈ MonoidHom.mrange f ↔ ∃ x, f x = y := Iff.rfl

