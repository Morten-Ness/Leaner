import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem map_mul₂ {_ : MulOneClass M} {_ : MulOneClass N} {_ : CommMonoid P} (f : M →* N →* P)
    (m₁ m₂ : M) (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n := (MonoidHom.flip f n).map_mul _ _

