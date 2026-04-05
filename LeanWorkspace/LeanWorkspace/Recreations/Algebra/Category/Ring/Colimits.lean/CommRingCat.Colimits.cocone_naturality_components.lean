import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (CommRingCat.Colimits.coconeMorphism F j') (F.map f x) = (CommRingCat.Colimits.coconeMorphism F j) x := by
  rw [← CommRingCat.Colimits.cocone_naturality F f, comp_apply]

