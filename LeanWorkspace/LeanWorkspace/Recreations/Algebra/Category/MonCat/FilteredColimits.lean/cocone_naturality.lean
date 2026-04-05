import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem cocone_naturality {j j' : J} (f : j ⟶ j') :
    F.map f ≫ MonCat.FilteredColimits.coconeMorphism.{v, u} F j' = MonCat.FilteredColimits.coconeMorphism F j := MonCat.ext fun x =>
    congr_fun ((Types.TypeMax.colimitCocone (F ⋙ forget MonCat)).ι.naturality f) x

