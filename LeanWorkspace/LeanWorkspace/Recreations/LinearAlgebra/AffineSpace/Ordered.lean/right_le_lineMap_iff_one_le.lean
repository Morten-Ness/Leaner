import Mathlib

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem right_le_lineMap_iff_one_le (h : a < b) : b ≤ lineMap a b r ↔ 1 ≤ r := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

