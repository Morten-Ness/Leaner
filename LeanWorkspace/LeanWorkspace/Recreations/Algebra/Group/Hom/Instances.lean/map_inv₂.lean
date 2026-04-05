import Mathlib

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

theorem map_inv₂ {_ : Group M} {_ : MulOneClass N} {_ : CommGroup P} (f : M →* N →* P) (m : M)
    (n : N) : f m⁻¹ n = (f m n)⁻¹ := (MonoidHom.flip f n).map_inv _

