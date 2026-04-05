import Mathlib

variable {R L : Type*} [CommRing R]

variable [LeftPreLieRing L]

theorem assoc_symm (x y z : L) :
    associator x y z = associator y x z := LeftPreLieRing.assoc_symm' x y z

