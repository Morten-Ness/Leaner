import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ CommRingCat.Colimits.coconeMorphism F j' = CommRingCat.Colimits.coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

