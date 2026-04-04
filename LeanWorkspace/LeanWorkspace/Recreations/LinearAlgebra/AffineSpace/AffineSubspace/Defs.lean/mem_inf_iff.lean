import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem mem_inf_iff (p : P) (s₁ s₂ : AffineSubspace k P) : p ∈ s₁ ⊓ s₂ ↔ p ∈ s₁ ∧ p ∈ s₂ := Iff.rfl

