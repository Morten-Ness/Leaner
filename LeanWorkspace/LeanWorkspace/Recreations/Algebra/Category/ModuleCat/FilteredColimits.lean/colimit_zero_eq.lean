import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_zero_eq (j : J) :
    0 = ModuleCat.FilteredColimits.M.mk F ⟨j, 0⟩ := by
  apply AddMonCat.FilteredColimits.colimit_zero_eq

