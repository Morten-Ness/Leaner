import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

theorem subtype_apply (x : S') :
    SubmonoidClass.subtype S' x = x := rfl

