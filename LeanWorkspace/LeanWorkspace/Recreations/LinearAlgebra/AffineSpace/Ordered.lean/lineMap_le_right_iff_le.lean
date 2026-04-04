import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_right_iff_le (h : r < 1) : lineMap a b r ≤ b ↔ a ≤ b := Iff.trans (by rw [lineMap_apply_one]) (lineMap_le_lineMap_iff_of_lt h)

