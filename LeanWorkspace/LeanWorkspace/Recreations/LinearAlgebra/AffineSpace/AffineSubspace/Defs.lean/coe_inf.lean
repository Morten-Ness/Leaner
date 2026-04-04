import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_inf (s₁ s₂ : AffineSubspace k P) : (s₁ ⊓ s₂ : Set P) = (s₁ : Set P) ∩ s₂ := rfl

