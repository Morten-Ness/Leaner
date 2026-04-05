import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [MulOneClass M] [SetLike A M] [hA : SubmonoidClass A M] (S' : A)

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem coe_subtype : ⇑S.subtype = Subtype.val := rfl

