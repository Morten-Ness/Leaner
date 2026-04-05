import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_one_eq (j : J) : (1 : M.{v, u} F) = M.mk F ⟨j, 1⟩ := by
  apply MonCat.FilteredColimits.M.mk_eq
  refine ⟨max' _ j, IsFiltered.leftToMax _ j, IsFiltered.rightToMax _ j, ?_⟩
  simp

