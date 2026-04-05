import Mathlib

variable {R L : Type*} [CommRing R]

variable [RightPreLieRing L]

theorem assoc_symm (x y z : L) :
    associator x y z = associator x z y := RightPreLieRing.assoc_symm' x y z

