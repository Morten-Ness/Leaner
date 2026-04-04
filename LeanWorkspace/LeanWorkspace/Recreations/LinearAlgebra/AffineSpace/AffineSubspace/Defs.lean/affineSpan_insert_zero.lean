import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_insert_zero (s : Set V) :
    (affineSpan k (insert 0 s) : Set V) = Submodule.span k s := by
  rw [← Submodule.span_insert_zero]
  refine affineSpan_subset_span.antisymm ?_
  rw [← vectorSpan_add_self, vectorSpan_def]
  refine Subset.trans ?_ <| subset_add_left _ <| mem_insert ..
  gcongr
  exact subset_sub_left <| mem_insert ..

