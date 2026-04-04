import Mathlib

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem lineMap_lt_left_iff_lt (h : 0 < r) : lineMap a b r < a ↔ b < a := left_lt_lineMap_iff_lt (E := Eᵒᵈ) h

