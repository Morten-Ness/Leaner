import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (spectrum.zero_mem_resolventSet_of_unit a)

