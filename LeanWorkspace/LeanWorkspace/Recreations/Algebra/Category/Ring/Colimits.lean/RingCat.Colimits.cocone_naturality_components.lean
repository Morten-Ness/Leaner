import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem cocone_naturality_components (j j' : J) (f : j ⟶ j') (x : F.obj j) :
    (RingCat.Colimits.coconeMorphism F j') (F.map f x) = (RingCat.Colimits.coconeMorphism F j) x := by
  rw [← RingCat.Colimits.cocone_naturality F f, comp_apply]

