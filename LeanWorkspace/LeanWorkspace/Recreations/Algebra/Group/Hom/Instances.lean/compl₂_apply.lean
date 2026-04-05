import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem compl₂_apply [MulOneClass M] [MulOneClass N] [CommMonoid P] [MulOneClass Q]
    (f : M →* N →* P) (g : Q →* N) (m : M) (q : Q) : (MonoidHom.compl₂ f g) m q = f m (g q) := rfl

