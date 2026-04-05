import Mathlib

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ MonCat.Colimits.coconeMorphism F j' = MonCat.Colimits.coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

