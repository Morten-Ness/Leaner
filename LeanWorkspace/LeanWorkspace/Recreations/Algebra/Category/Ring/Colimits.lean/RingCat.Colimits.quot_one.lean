import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem quot_one : Quot.mk Setoid.r one = (1 : RingCat.Colimits.ColimitType F) := rfl

