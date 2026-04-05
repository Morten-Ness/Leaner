import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem mul_apply {M N} [One M] [MulOneClass N] (f g : OneHom M N) (x : M) :
    (f * g) x = f x * g x := rfl

