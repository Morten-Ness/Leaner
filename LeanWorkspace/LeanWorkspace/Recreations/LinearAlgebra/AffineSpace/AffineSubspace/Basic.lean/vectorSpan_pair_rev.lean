import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ (p₂ -ᵥ p₁) := by
  rw [pair_comm, vectorSpan_pair]

