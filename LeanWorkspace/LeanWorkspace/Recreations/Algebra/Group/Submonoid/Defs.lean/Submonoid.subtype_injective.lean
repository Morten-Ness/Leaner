import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem subtype_injective (s : Submonoid M) :
    Function.Injective s.subtype := Subtype.coe_injective

