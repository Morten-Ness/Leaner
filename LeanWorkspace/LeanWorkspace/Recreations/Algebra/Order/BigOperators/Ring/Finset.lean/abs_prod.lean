import Mathlib

variable {ι R S : Type*}

theorem abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι) (f : ι → R) :
    |∏ x ∈ s, f x| = ∏ x ∈ s, |f x| := map_prod absHom _ _

