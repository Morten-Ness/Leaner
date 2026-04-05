import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem ι_colimitDesc (t : Cocone F) (j : J) :
    (ModuleCat.FilteredColimits.colimitCocone F).ι.app j ≫ ModuleCat.FilteredColimits.colimitDesc F t = t.ι.app j := (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

