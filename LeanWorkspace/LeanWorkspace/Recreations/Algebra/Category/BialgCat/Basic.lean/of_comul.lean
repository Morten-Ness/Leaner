import Mathlib

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem of_comul {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.comul (A := BialgCat.of R X) = Coalgebra.comul (R := R) (A := X) := rfl

