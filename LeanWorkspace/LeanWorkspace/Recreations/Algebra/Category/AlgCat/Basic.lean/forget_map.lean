import Mathlib

variable (R : Type u) [CommRing R]

theorem forget_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (forget (AlgCat.{v} R)).map f = (f : _ → _) := rfl

