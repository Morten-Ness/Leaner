import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem StrictMonoOn.slope_pos {s : Set k} (hf : StrictMonoOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : 0 < slope f x y := by
  rcases lt_or_gt_of_ne hxy with hxy | hxy
  · exact (slope_pos_iff_of_le hxy.le).mpr (hf hx hy hxy)
  · exact slope_comm f x y ▸ (slope_pos_iff_of_le hxy.le).mpr (hf hy hx hxy)

