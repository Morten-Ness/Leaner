import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show CommRingCat.Colimits.ColimitType F from Quot.mk _ x) * (show CommRingCat.Colimits.ColimitType F from Quot.mk _ y) := rfl

