import Mathlib

variable (R : Type u) [CommRing R]

theorem forget₂_module_obj (X : AlgCat.{v} R) :
    (forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X := rfl

