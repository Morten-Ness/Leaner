import Mathlib

variable {R : Type u} [Ring R] {J : Type v} [SmallCategory J] [IsFiltered J]

variable (F : J ⥤ ModuleCat.{max v u, u} R)

theorem M.mk_surjective (m : ModuleCat.FilteredColimits.M F) :
    ∃ (j : J) (x : F.obj j), ModuleCat.FilteredColimits.M.mk F ⟨j, x⟩ = m := (F ⋙ forget (ModuleCat R)).ιColimitType_jointly_surjective m

