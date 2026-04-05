import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem LieAlgebra.isNilpotent_ad_of_isNilpotent
    {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) :
    IsNilpotent (LieAlgebra.ad R L x) := L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent h

