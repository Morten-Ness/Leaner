import Mathlib

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem G.mk_eq (x y : Σ j, F.obj j)
    (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
    G.mk.{v, u} F x = G.mk F y := Quot.eqvGen_sound (Types.FilteredColimit.eqvGen_colimitTypeRel_of_rel (F ⋙ forget GrpCat) x y h)

end

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y) :
    GrpCat.FilteredColimits.colimitInvAux.{v, u} F x = GrpCat.FilteredColimits.colimitInvAux F y := by
  apply GrpCat.FilteredColimits.G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv, map_inv, inv_inj]
  exact hfg

end

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    G.mk.{v, u} F ⟨j, x⟩ * G.mk.{v, u} F ⟨j, y⟩ = G.mk.{v, u} F ⟨j, x * y⟩ := by
  #adaptation_note /-- Prior to leanprover/lean4#12564, this was just
  `simpa using GrpCat.FilteredColimits.colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)` -/
  have := GrpCat.FilteredColimits.colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)
  simpa using this

end

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_mul_mk_eq (x y : Σ j, F.obj j) (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k) :
    G.mk.{v, u} F x * G.mk F y = G.mk F ⟨k, F.map f x.2 * F.map g y.2⟩ := MonCat.FilteredColimits.colimit_mul_mk_eq _ _ _ _ _ _

end

section

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩ := MonCat.FilteredColimits.colimit_one_eq _ _

end
