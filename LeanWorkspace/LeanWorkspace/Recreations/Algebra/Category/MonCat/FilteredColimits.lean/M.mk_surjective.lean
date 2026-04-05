import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ MonCat.{max v u})

theorem M.mk_surjective (m : M.{v, u} F) :
    ∃ (j : J) (x : F.obj j), M.mk F ⟨j, x⟩ = m := (F ⋙ forget MonCat).ιColimitType_jointly_surjective m

