import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_le {s₁ s₂ : AffineSubspace k P} (h : s₁ ≤ s₂) : s₁.direction ≤ s₂.direction := by
  simp only [AffineSubspace.direction_eq_vectorSpan, vectorSpan_def]
  exact vectorSpan_mono k h

