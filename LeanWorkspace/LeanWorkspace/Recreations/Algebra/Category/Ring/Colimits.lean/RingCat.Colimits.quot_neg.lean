import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ RingCat.{v})

theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show RingCat.Colimits.ColimitType F from Quot.mk Setoid.r x) := rfl

