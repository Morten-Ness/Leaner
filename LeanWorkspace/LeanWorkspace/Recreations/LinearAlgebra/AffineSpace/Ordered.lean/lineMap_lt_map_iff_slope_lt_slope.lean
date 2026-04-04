import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_lt_map_iff_slope_lt_slope (hab : a < b) (h₀ : 0 < r) (h₁ : r < 1) :
    lineMap (f a) (f b) r < f c ↔ slope f c b < slope f a c := map_lt_lineMap_iff_slope_lt_slope (E := Eᵒᵈ) hab h₀ h₁

