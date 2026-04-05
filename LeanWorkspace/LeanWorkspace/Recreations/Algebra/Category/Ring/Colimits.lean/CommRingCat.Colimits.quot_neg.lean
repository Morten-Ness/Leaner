import Mathlib

variable {J : Type v} [SmallCategory J] (F : J ⥤ CommRingCat.{v})

theorem quot_neg (x : Prequotient F) :
    Quot.mk Setoid.r (neg x) = -(show CommRingCat.Colimits.ColimitType F from Quot.mk Setoid.r x) := rfl

-- Porting note: Lean can't see `Quot.mk Setoid.r x` is a `CommRingCat.Colimits.ColimitType F` even with type annotation
-- unless we use `by exact` to change the elaboration order.

