import Mathlib

variable {k E PE : Type*}

variable [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]
  {a a' b b' : E} {r r' : k}

theorem midpoint_le_midpoint [Invertible (2 : k)] (ha : a ≤ a') (hb : b ≤ b') :
    midpoint k a b ≤ midpoint k a' b' := lineMap_mono_endpoints ha hb (invOf_nonneg.2 zero_le_two) <| invOf_le_one one_le_two

