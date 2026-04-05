import Mathlib

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (MonCat.Colimits.coconeMorphism F j') (F.map f x) = (MonCat.Colimits.coconeMorphism F j) x := by
  rw [← MonCat.Colimits.cocone_naturality F f]
  rfl

