import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem quot_one : Quot.mk Setoid.r one = (1 : CommRingCat.Colimits.ColimitType F) := rfl

