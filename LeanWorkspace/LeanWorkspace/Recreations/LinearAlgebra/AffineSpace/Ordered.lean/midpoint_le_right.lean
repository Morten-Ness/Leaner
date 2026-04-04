import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {a b : E} {r r' : k}

theorem midpoint_le_right : midpoint k a b ≤ b ↔ a ≤ b := lineMap_le_right_iff_le two_inv_lt_one

