import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem restrict_apply {N S : Type*} [MulOneClass N] [SetLike S M] [SubmonoidClass S M]
    (f : M →* N) (s : S) (x : s) : f.restrict s x = f x := rfl

