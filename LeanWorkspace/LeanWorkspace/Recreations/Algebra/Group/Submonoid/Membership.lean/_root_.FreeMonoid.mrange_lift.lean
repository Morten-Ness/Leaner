import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem _root_.FreeMonoid.mrange_lift {α} (f : α → M) :
    mrange (FreeMonoid.lift f) = closure (Set.range f) := by
  rw [mrange_eq_map, ← FreeMonoid.closure_range_of, map_mclosure, ← Set.range_comp,
    FreeMonoid.lift_comp_of]

