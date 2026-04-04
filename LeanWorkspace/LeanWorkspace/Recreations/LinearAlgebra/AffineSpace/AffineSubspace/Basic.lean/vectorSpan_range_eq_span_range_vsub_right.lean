import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

theorem vectorSpan_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i -ᵥ p i0) := by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0), ← Set.range_comp]
  congr

