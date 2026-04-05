import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem add_mem_add_iff {a : A} {r s : R} : r + s ∈ σ (↑ₐ s + a) ↔ r ∈ σ a := by
  rw [spectrum.add_mem_iff, neg_add_cancel_left]

