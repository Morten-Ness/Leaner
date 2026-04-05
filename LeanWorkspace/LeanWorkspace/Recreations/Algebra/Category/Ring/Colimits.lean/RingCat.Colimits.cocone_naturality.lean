import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ RingCat.Colimits.coconeMorphism F j' = RingCat.Colimits.coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

