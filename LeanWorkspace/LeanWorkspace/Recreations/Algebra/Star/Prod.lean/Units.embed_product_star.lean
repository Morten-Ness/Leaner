import Mathlib

variable {R : Type u} {S : Type v}

theorem Units.embed_product_star [Monoid R] [StarMul R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) := rfl

