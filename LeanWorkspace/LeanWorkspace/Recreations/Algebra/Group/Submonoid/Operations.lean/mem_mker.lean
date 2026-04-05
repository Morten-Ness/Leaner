import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mem_mker {f : F} {x : M} : x ∈ MonoidHom.mker f ↔ f x = 1 := Iff.rfl

