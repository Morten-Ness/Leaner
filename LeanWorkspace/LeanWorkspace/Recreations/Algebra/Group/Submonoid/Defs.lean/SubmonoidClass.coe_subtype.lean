import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

theorem coe_subtype : (SubmonoidClass.subtype S' : S' → M) = Subtype.val := rfl

