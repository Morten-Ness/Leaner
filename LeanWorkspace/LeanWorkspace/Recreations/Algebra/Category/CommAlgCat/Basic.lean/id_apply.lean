import Mathlib

variable {R : Type u} [CommRing R]

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

theorem id_apply (A : CommAlgCat.{v} R) (a : A) : (𝟙 A : A ⟶ A) a = a := by simp

