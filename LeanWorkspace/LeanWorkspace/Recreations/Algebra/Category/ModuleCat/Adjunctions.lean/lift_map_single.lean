import Mathlib

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

variable {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    (CategoryTheory.Free.lift R F).map (single f r) = r • F.map f := by simp

