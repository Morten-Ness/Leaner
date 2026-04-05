import Mathlib

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimitInvAux_eq_of_rel (x y : Σ j, F.obj j)
    (h : Types.FilteredColimit.Rel (F ⋙ forget GrpCat) x y) :
    GrpCat.FilteredColimits.colimitInvAux.{v, u} F x = GrpCat.FilteredColimits.colimitInvAux F y := by
  apply GrpCat.FilteredColimits.G.mk_eq
  obtain ⟨k, f, g, hfg⟩ := h
  use k, f, g
  rw [map_inv, map_inv, inv_inj]
  exact hfg

