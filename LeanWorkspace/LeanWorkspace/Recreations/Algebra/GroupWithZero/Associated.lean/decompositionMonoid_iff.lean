import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem decompositionMonoid_iff : DecompositionMonoid (Associates M) ↔ DecompositionMonoid M := by
  simp_rw [_root_.decompositionMonoid_iff, Associates.forall_associated, Associates.isPrimal_mk]

