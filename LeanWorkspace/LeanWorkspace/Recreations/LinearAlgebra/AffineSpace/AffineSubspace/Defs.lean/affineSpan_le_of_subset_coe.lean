import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k}

theorem affineSpan_le_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    affineSpan k s ≤ s₁ := AffineSubspace.spanPoints_subset_coe_of_subset_coe h

