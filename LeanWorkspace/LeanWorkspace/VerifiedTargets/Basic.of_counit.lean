import Mathlib

variable (R : Type u) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem of_counit {X : Type v} [Ring X] [Bialgebra R X] :
    Coalgebra.counit (A := BialgCat.of R X) = Coalgebra.counit (R := R) (A := X) := rfl

