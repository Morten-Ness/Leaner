import Mathlib

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem left_lt_lineMap_iff_pos (h : a < b) : a < lineMap a b r ↔ 0 < r := by
  rw [← lineMap_lt_lineMap_iff_of_lt' h, lineMap_apply_zero]

