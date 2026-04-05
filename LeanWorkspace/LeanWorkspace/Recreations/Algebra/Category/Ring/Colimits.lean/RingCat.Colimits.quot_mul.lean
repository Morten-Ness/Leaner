import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem quot_mul (x y) :
    Quot.mk Setoid.r (mul x y) =
      (show RingCat.Colimits.ColimitType F from Quot.mk _ x) * (show RingCat.Colimits.ColimitType F from Quot.mk _ y) := rfl

