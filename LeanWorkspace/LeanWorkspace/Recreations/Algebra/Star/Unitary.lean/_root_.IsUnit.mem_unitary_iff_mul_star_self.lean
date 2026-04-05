import Mathlib

variable {R : Type*}

variable [Monoid R] [StarMul R]

theorem _root_.IsUnit.mem_unitary_iff_mul_star_self {u : R} (hu : IsUnit u) :
    u ∈ unitary R ↔ u * star u = 1 := by
  rw [← Unitary.star_mem_iff, hu.star.mem_unitary_iff_star_mul_self, star_star]

alias ⟨_, _root_.IsUnit.mem_unitary_of_star_mul_self⟩ := IsUnit.mem_unitary_iff_star_mul_self
alias ⟨_, _root_.IsUnit.mem_unitary_of_mul_star_self⟩ := IsUnit.mem_unitary_iff_mul_star_self

