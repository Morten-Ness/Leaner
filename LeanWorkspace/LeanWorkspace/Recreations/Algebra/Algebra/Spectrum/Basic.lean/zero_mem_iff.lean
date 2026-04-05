import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬IsUnit a := by
  rw [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff

