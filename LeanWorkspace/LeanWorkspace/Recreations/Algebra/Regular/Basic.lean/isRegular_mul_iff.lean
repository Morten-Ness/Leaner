import Mathlib

variable {R : Type*}

variable [CommSemigroup R] {a b : R}

theorem isRegular_mul_iff : IsRegular (a * b) ↔ IsRegular a ∧ IsRegular b := by
  refine Iff.trans ?_ isRegular_mul_and_mul_iff
  exact ⟨fun ab => ⟨ab, by rwa [mul_comm]⟩, fun rab => rab.1⟩

