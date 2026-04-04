import Mathlib

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem lineMap_le_right_iff_le_one (h : a < b) : lineMap a b r ≤ b ↔ r ≤ 1 := by
  rw [← lineMap_le_lineMap_iff_of_lt' h, lineMap_apply_one]

