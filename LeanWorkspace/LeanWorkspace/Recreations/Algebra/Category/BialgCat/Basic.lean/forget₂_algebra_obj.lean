import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_algebra_obj (X : BialgCat R) :
    (forget₂ (BialgCat R) (AlgCat R)).obj X = AlgCat.of R X := rfl

