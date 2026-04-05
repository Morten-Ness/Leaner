import Mathlib

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem quot_one : Quot.mk Setoid.r one = (1 : MonCat.Colimits.ColimitType F) := rfl

