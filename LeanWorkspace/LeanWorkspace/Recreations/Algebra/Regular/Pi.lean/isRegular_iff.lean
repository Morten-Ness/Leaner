import Mathlib

variable {ι α : Type*} {R : ι → Type*}

variable [∀ i, Mul (R i)]

theorem isRegular_iff {a : ∀ i, R i} : IsRegular a ↔ ∀ i, IsRegular (a i) := by
  simp [_root_.isRegular_iff, forall_and]

