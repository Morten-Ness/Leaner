import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem forget_obj (A : CommBialgCat.{v} R) : (forget (CommBialgCat.{v} R)).obj A = A := rfl

