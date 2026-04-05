import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem flip_apply {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (x : M) (y : N) : f.flip y x = f x y := rfl

