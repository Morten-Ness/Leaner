import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x := congr_fun ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

