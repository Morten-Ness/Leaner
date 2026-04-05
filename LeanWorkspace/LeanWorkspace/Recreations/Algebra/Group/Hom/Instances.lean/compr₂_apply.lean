import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem compr₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q] (f : M →* N →* P)
    (g : P →* Q) (m : M) (n : N) : (MonoidHom.compr₂ f g) m n = g (f m n) := rfl

