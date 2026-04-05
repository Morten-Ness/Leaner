import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_obj (X : CoalgCat R) :
    (forget₂ (CoalgCat R) (ModuleCat R)).obj X = ModuleCat.of R X := rfl

