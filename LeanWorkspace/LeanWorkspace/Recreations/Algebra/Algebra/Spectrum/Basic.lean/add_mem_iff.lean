import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem add_mem_iff {a : A} {r s : R} : r + s ∈ σ a ↔ r ∈ σ (-↑ₐ s + a) := by
  simp only [spectrum.mem_iff, sub_neg_eq_add, ← sub_sub, map_add]

