import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem left_le_lineMap_iff_le (h : 0 < r) : a ≤ lineMap a b r ↔ a ≤ b := Iff.trans (by rw [lineMap_apply_zero]) (lineMap_le_lineMap_iff_of_lt h)

