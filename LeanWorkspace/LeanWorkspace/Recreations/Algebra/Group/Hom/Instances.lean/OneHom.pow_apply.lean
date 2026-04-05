import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem OneHom.pow_apply [One M] [Monoid N] (f : OneHom M N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n := rfl

