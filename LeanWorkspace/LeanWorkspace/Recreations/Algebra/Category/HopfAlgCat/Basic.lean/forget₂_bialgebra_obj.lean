import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_bialgebra_obj (X : HopfAlgCat R) :
    (forget₂ (HopfAlgCat R) (BialgCat R)).obj X = BialgCat.of R X := rfl

