import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem mul_apply {M N} [Mul M] [CommSemigroup N] (f g : M →ₙ* N) (x : M) :
    (f * g) x = f x * g x := rfl

