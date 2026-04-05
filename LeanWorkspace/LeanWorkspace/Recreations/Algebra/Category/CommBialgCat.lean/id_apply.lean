import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem id_apply (A : CommBialgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

