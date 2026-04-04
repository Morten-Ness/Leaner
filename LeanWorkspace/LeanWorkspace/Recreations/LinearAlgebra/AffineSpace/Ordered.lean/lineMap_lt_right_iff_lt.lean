import Mathlib

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem lineMap_lt_right_iff_lt (h : r < 1) : lineMap a b r < b ↔ a < b := Iff.trans (by rw [lineMap_apply_one]) (lineMap_lt_lineMap_iff_of_lt h)

