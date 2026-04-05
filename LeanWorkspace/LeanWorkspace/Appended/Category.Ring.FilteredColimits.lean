import Mathlib

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descAddMonoidHom_quotMk {j : J} (x : F.obj j) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x := congr_fun ((forget AddCommMonCat).congr_map
    ((AddCommMonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ SemiRingCat AddCommMonCat)).fac
        ((forget₂ SemiRingCat AddCommMonCat).mapCocone t) j)) x

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descMonoidHom_apply_eq (x : R F) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom t x = SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom t x := by
  obtain ⟨j, x⟩ := x
  rw [SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom_quotMk t x, SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descAddMonoidHom_quotMk t x]

end

section

variable {J : Type v} [SmallCategory J] (F : J ⥤ SemiRingCat.{max v u})

variable [IsFiltered J]

variable {F} (t : Cocone F)

theorem descMonoidHom_quotMk {j : J} (x : F.obj j) :
    SemiRingCat.FilteredColimits.colimitCoconeIsColimit.descMonoidHom t (Quot.mk _ ⟨j, x⟩) = t.ι.app j x := congr_fun ((forget MonCat).congr_map
    ((MonCat.FilteredColimits.colimitCoconeIsColimit.{v, u}
      (F ⋙ forget₂ _ _)).fac ((forget₂ _ _).mapCocone t) j)) x

end
