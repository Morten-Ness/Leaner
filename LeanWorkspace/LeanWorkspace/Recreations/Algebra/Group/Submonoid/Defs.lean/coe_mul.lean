import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y := rfl

