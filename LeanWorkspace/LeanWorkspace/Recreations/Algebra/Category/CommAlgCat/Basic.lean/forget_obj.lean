import Mathlib

variable {R : Type u} [CommRing R]

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

theorem forget_obj (A : CommAlgCat.{v} R) : (forget (CommAlgCat.{v} R)).obj A = A := rfl

