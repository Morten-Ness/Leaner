import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

variable {A B C : CommBialgCat.{v} R} {X Y Z : Type v} [CommRing X] [Bialgebra R X]
  [CommRing Y] [Bialgebra R Y] [CommRing Z] [Bialgebra R Z]

theorem hom_inv_apply (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by simp

