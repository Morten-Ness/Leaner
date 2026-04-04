import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

theorem vectorSpan_image_eq_span_vsub_set_right_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' (p '' (s \ {i}))) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi,
      ← Set.insert_diff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

