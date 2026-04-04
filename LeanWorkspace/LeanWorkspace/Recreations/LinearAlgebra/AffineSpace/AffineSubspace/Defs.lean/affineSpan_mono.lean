import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_mono {s₁ s₂ : Set P} (h : s₁ ⊆ s₂) : affineSpan k s₁ ≤ affineSpan k s₂ := affineSpan_le_of_subset_coe (Set.Subset.trans h (subset_affineSpan k _))

