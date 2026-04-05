import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

variable [IsFiltered J]

theorem colimit_mul_mk_eq' {j : J} (x y : F.obj j) :
    M.mk.{v, u} F ⟨j, x⟩ * M.mk.{v, u} F ⟨j, y⟩ = M.mk.{v, u} F ⟨j, x * y⟩ := by
  simpa using MonCat.FilteredColimits.colimit_mul_mk_eq F ⟨j, x⟩ ⟨j, y⟩ j (𝟙 _) (𝟙 _)

