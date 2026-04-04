import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem left_le_midpoint : a ≤ midpoint k a b ↔ a ≤ b := left_le_lineMap_iff_le <| inv_pos.2 zero_lt_two

