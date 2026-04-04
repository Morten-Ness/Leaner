import Mathlib

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

variable [PosSMulReflectLT k E]

theorem right_lt_lineMap_iff_lt (h : r < 1) : b < lineMap a b r ↔ b < a := lineMap_lt_right_iff_lt (E := Eᵒᵈ) h

