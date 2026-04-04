import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem right_le_lineMap_iff_le (h : r < 1) : b ≤ lineMap a b r ↔ b ≤ a := lineMap_le_right_iff_le (E := Eᵒᵈ) h

