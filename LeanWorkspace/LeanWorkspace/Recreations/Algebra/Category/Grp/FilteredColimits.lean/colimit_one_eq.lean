import Mathlib

variable {J : Type v} [SmallCategory J] [IsFiltered J] (F : J ⥤ GrpCat.{max v u})

theorem colimit_one_eq (j : J) : (1 : G.{v, u} F) = G.mk F ⟨j, 1⟩ := MonCat.FilteredColimits.colimit_one_eq _ _

