import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem subtype_apply (x : S') :
    MulMemClass.subtype S' x = x := rfl

