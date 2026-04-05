import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descMonoidHom_apply_eq (x : R F) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom t x = SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom_quotMk t x, SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom_quotMk t x]

