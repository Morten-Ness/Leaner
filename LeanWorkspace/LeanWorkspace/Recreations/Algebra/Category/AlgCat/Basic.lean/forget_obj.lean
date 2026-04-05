import Mathlib

variable (R : Type u) [CommRing R]

theorem forget_obj {A : AlgCat.{v} R} : (forget (AlgCat.{v} R)).obj A = A := rfl

