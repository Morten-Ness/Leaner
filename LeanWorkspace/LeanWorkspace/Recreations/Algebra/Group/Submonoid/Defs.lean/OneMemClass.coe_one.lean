import Mathlib

variable {M : Type*} {N : Type*}

variable {A M₁ : Type*} [SetLike A M₁] [One M₁] [hA : OneMemClass A M₁] (S' : A)

theorem coe_one : ((1 : S') : M₁) = 1 := rfl

