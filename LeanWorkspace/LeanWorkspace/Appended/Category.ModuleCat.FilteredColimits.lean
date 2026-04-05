import Mathlib

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) : ModuleCat.FilteredColimits.M.mk F x = ModuleCat.FilteredColimits.M.mk F y := Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel
    (F ⋙ forget (ModuleCat R)) x y h)

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    ModuleCat.FilteredColimits.M.mk F ⟨k, F.map f x⟩ = ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ := ModuleCat.FilteredColimits.M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_surjective (m : ModuleCat.FilteredColimits.M F) :
    ∃ (j : J) (x : F.obj j), ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ = m := (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimitSMulAux_eq_of_rel (r : R) (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget (ModuleCat R)) x y) :
    ModuleCat.FilteredColimits.colimitSMulAux F r x = ModuleCat.FilteredColimits.colimitSMulAux F r y := by
  apply ModuleCat.FilteredColimits.M.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  simp only [Functor.comp_obj, Functor.comp_map, forget_map] at hfg
  simp [hfg]

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_add_mk_eq' {j : J} (x y : F.obj j) :
    ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ + ModuleCat.FilteredColimits.M.mk F ⟨j, y⟩ = ModuleCat.FilteredColimits.M.mk F ⟨j, x + y⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_add_mk_eq (x y : Σ j, F.obj j) (k : J)
    (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    ModuleCat.FilteredColimits.M.mk _ x + ModuleCat.FilteredColimits.M.mk _ y = ModuleCat.FilteredColimits.M.mk _ ⟨k, F.map f x.2 + F.map g y.2⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_smul_mk_eq (r : R) (x : Σ j, F.obj j) : r • ModuleCat.FilteredColimits.M.mk F x = ModuleCat.FilteredColimits.M.mk F ⟨x.1, r • x.2⟩ := rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11083): writing directly the `Module` instance makes things very slow.

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_zero_eq (j : J) :
    0 = ModuleCat.FilteredColimits.M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

end

section

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem ι_colimitDesc (t : Cocone F) (j : J) :
    (ModuleCat.FilteredColimits.colimitCocone F).ι.app j ≫ ModuleCat.FilteredColimits.colimitDesc F t = t.ι.app j := (forget₂ _ AddCommGrpCat).map_injective
    ((AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit (F ⋙ forget₂ _ _)).fac _ _)

end
