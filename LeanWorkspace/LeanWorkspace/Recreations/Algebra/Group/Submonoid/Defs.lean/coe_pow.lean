import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

theorem coe_pow {M} [Monoid M] {A : Type*} [SetLike A M] [SubmonoidClass A M] {S : A} (x : S)
    (n : ℕ) : ↑(x ^ n) = (x : M) ^ n := rfl

