import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem slope_nonneg_iff_of_le (hxy : x ≤ y) : 0 ≤ slope f x y ↔ f x ≤ f y := by
  by_cases hxeqy : x = y
  · simp [hxeqy]
  refine ⟨fun h ↦ ?_, fun h ↦ smul_nonneg (inv_nonneg.2 (sub_nonneg.2 hxy)) ?_⟩
  · have := smul_nonneg (sub_nonneg.2 hxy) h
    rwa [slope, ← mul_smul, mul_inv_cancel₀ (mt sub_eq_zero.1 (Ne.symm hxeqy)), one_smul,
      vsub_eq_sub, sub_nonneg] at this
  · rwa [vsub_eq_sub, sub_nonneg]

