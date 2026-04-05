import Mathlib

section

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ MonCat.Colimits.coconeMorphism F j' = MonCat.Colimits.coconeMorphism F j := by
  ext
  apply Quot.sound
  apply Relation.map

end

section

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (MonCat.Colimits.coconeMorphism F j') (F.map f x) = (MonCat.Colimits.coconeMorphism F j) x := by
  rw [← MonCat.Colimits.cocone_naturality F f]
  rfl

end
