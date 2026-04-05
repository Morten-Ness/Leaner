import Mathlib

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

set_option backward.isDefEq.respectTransparency false in
theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : CategoryTheory.Free.of R X ⟶ CategoryTheory.Free.of R Z) = single (f ≫ g) (r * s) := by
  dsimp +instances [CategoryTheory.categoryFree]
  simp

