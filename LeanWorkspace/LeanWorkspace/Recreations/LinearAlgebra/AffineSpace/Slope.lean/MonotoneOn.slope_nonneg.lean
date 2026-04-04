import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem MonotoneOn.slope_nonneg {s : Set k} (hf : MonotoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    0 ≤ slope f x y := by
  rcases le_total x y with hxy | hxy
  · exact (slope_nonneg_iff_of_le hxy).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_nonneg_iff_of_le hxy).mpr (hf hy hx hxy)

