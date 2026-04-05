import Mathlib

variable {R : Type*}

variable [Monoid R] {a b : R} {n : ℕ}

theorem IsUnit.isRegular (ua : IsUnit a) : IsRegular a := by
  rcases ua with ⟨a, rfl⟩
  exact Units.isRegular a

