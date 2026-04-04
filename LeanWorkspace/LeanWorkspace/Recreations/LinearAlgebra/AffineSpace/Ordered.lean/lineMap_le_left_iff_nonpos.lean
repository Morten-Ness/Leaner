import Mathlib

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_left_iff_nonpos (h : a < b) : lineMap a b r ≤ a ↔ r ≤ 0 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_zero]

