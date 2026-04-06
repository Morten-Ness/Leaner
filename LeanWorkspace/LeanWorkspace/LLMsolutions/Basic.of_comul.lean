import Mathlib

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := X) = (Bialgebra.toCoalgebra (R := R) (A := X)).comul := rfl
