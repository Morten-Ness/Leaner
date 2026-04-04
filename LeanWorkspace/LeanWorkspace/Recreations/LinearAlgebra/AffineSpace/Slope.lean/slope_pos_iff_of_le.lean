import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_pos_iff_of_le (hxy : x ≤ y) : 0 < slope f x y ↔ f x < f y := by
  simp_rw [lt_iff_le_and_ne, slope_nonneg_iff_of_le hxy, Ne, eq_comm, slope_eq_zero_iff]

