import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem MonoidHom.pow_apply [MulOneClass M] [CommMonoid N] (f : M →* N) (n : ℕ) (x : M) :
    (f ^ n) x = f x ^ n := rfl

