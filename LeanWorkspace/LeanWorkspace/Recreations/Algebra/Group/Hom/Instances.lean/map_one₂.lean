import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem map_one₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (n : N) : f 1 n = 1 := (MonoidHom.flip f n).map_one

