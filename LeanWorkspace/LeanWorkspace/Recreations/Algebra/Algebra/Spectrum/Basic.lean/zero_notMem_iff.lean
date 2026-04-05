import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [spectrum.zero_mem_iff, Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

