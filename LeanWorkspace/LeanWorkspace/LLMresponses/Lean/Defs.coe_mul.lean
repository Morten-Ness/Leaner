import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y := rfl
