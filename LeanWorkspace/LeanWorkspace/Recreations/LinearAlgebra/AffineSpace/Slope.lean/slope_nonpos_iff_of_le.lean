import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_nonpos_iff_of_le (hxy : x ≤ y) : slope f x y ≤ 0 ↔ f y ≤ f x := by
  simpa using slope_nonneg_iff_of_le (f := -f) hxy

