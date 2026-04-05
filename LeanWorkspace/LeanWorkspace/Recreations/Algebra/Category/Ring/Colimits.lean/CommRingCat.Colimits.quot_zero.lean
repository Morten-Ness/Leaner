import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem quot_zero : Quot.mk Setoid.r zero = (0 : CommRingCat.Colimits.ColimitType F) := rfl

