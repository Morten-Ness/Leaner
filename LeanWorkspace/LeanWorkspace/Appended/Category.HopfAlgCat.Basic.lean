import Mathlib

section

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem of_comul {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

end

section

variable (R : Type u) [CommRing R]

theorem of_counit {X : Type v} [Ring X] [HopfAlgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

end
