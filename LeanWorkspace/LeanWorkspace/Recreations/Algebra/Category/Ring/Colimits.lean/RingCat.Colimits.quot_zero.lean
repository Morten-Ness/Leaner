import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem quot_zero : Quot.mk Setoid.r zero = (0 : RingCat.Colimits.ColimitType F) := rfl

