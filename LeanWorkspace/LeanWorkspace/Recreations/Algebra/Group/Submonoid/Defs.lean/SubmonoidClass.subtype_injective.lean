import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

theorem subtype_injective :
    Function.Injective (SubmonoidClass.subtype S') := Subtype.coe_injective

