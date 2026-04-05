import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem OneHom.zpow_apply [One M] [Group N] (f : OneHom M N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z := rfl

