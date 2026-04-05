import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

theorem smul_lowerBounds_subset_upperBounds_smul (ha : a ≤ 0) :
    a • lowerBounds s ⊆ upperBounds (a • s) := (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image

