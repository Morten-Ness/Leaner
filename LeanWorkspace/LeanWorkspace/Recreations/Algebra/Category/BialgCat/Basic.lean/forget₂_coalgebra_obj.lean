import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_coalgebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (CoalgCat R)).obj X = CoalgCat.of R X := rfl

