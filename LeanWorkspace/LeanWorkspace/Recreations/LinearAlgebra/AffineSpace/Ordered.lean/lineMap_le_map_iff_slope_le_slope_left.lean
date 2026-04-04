import Mathlib

variable {k E PE : Type*}

variable [Field k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]

variable [Module k E] [IsStrictOrderedModule k E] [PosSMulReflectLE k E]

variable {f : k → E} {a b r : k}

theorem lineMap_le_map_iff_slope_le_slope_left (h : 0 < r * (b - a)) :
    lineMap (f a) (f b) r ≤ f c ↔ slope f a b ≤ slope f a c := map_le_lineMap_iff_slope_le_slope_left (E := Eᵒᵈ) (f := f) (a := a) (b := b) (r := r) h

