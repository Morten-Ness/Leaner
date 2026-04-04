import Mathlib

variable {k E PE : Type*}

variable [Ring k] [PartialOrder k] [IsOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module k E] [IsStrictOrderedModule k E]

variable {a a' b b' : E} {r r' : k}

theorem lineMap_strict_mono_endpoints (ha : a < a') (hb : b < b') (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    lineMap a b r < lineMap a' b' r := by
  rcases h₀.eq_or_lt with (rfl | h₀); · simpa
  exact (lineMap_mono_left ha.le h₁).trans_lt (lineMap_strict_mono_right hb h₀)

