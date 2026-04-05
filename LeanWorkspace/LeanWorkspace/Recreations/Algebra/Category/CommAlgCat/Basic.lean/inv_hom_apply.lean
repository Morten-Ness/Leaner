import Mathlib

variable {R : Type u} [CommRing R]

variable {A B C : CommAlgCat.{v} R} {X Y Z : Type v} [CommRing X] [Algebra R X]
  [CommRing Y] [Algebra R Y] [CommRing Z] [Algebra R Z]

theorem inv_hom_apply (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by simp

