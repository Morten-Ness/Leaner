import Mathlib

variable {J : Type v} [Category.{u} J] (F : J ⥤ MonCat.{v})

theorem quot_mul (x y : Prequotient F) : Quot.mk Setoid.r (mul x y) =
    @HMul.hMul (MonCat.Colimits.ColimitType F) (MonCat.Colimits.ColimitType F) (MonCat.Colimits.ColimitType F) _
      (Quot.mk Setoid.r x) (Quot.mk Setoid.r y) := rfl

