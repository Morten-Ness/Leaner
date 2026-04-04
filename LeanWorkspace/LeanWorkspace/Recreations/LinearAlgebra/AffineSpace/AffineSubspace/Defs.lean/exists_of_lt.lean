import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem exists_of_lt {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂) : ∃ p ∈ s₂, p ∉ s₁ := Set.exists_of_ssubset h

