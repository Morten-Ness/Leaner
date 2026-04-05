import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_map {j k : J} (f : j ⟶ k) (x : F.obj j) :
    ModuleCat.FilteredColimits.M.mk F ⟨k, F.map f x⟩ = ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ := ModuleCat.FilteredColimits.M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

