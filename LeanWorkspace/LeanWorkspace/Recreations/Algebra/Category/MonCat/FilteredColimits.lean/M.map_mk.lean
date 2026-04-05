import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.map_mk {j k : J} (f : j ⟶ k) (x : F.obj j) :
    M.mk F ⟨k, F.map f x⟩ = M.mk F ⟨j, x⟩ := MonCat.FilteredColimits.M.mk_eq _ _ _ ⟨k, 𝟙 _, f, by simp⟩

