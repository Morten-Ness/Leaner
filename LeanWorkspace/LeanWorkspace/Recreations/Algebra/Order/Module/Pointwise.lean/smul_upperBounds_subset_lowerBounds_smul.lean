import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

theorem smul_upperBounds_subset_lowerBounds_smul (ha : a ≤ 0) :
    a • upperBounds s ⊆ lowerBounds (a • s) := (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image

