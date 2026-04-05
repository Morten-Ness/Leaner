import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem colimit_add_mk_eq' {j : J} (x y : F.obj j) :
    ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ + ModuleCat.FilteredColimits.M.mk F ⟨j, y⟩ = ModuleCat.FilteredColimits.M.mk F ⟨j, x + y⟩ := by
  apply AddMonCat.FilteredColimits.colimit_add_mk_eq'

