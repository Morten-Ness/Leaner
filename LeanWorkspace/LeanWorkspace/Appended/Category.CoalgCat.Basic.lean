import Mathlib

section

variable (R : Type u) [CommRing R]

theorem of_comul {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.comul (A := of R X) = Coalgebra.comul (R := R) (A := X) := rfl

end

section

variable (R : Type u) [CommRing R]

theorem of_counit {X : Type v} [AddCommGroup X] [Module R X] [Coalgebra R X] :
    Coalgebra.counit (A := of R X) = Coalgebra.counit (R := R) (A := X) := rfl

end
