import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem map_div₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ / m₂) n = f m₁ n / f m₂ n := (MonoidHom.flip f n).map_div _ _

