import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_subset_span {s : Set V} :
    (affineSpan k s : Set V) ⊆ Submodule.span k s := affineSpan_le_toAffineSubspace_span

-- TODO: We want this to be simp, but `affineSpan` gets simp-ed away to `spanPoints`!
-- Let's delete `spanPoints`

