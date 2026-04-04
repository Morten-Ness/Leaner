import Mathlib

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem left_lt_lineMap_iff_lt (h : 0 < r) : a < lineMap a b r ↔ a < b := Iff.trans (by rw [lineMap_apply_zero]) (lineMap_lt_lineMap_iff_of_lt h)

