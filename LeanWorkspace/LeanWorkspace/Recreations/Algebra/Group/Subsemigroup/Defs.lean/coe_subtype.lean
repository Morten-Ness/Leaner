import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem coe_subtype : (MulMemClass.subtype S' : S' → M) = Subtype.val := rfl

