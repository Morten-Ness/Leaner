import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem mem_prod {s : Submonoid M} {t : Submonoid N} {p : M × N} :
    p ∈ s.prod t ↔ p.1 ∈ s ∧ p.2 ∈ t := Iff.rfl

