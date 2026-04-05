import Mathlib

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_inv_mk_eq (x : Σ j, F.obj j) : (G.mk.{v, u} F x)⁻¹ = G.mk F ⟨x.1, x.2⁻¹⟩ := rfl

