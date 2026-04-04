import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

theorem vectorSpan_eq_span_vsub_finset_right_ne [DecidableEq P] [DecidableEq V] {s : Finset P}
    {p : P} (hp : p ∈ s) :
    vectorSpan k (s : Set P) = Submodule.span k ((s.erase p).image (· -ᵥ p)) := by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

