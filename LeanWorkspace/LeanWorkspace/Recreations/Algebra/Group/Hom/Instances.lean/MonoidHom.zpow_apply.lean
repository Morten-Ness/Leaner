import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem MonoidHom.zpow_apply [MulOneClass M] [CommGroup N] (f : M →* N) (z : ℤ) (x : M) :
    (f ^ z) x = f x ^ z := rfl

