import Mathlib

variable {R : Type u} [CommRing R]

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

theorem comp_apply (f : A ⟶ B) (g : B ⟶ C) (a : A) : (f ≫ g) a = g (f a) := by simp

