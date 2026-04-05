import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descMonoidHom_quotMk {j : J} (x : F.obj j) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x := congr_fun ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

