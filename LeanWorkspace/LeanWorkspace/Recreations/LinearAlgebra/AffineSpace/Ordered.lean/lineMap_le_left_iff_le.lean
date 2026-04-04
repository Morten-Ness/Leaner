import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem lineMap_le_left_iff_le (h : 0 < r) : lineMap a b r ≤ a ↔ b ≤ a := left_le_lineMap_iff_le (E := Eᵒᵈ) h

