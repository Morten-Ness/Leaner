import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem coe_eq_bot_iff (Q : AffineSubspace k P) : (Q : Set P) = ∅ ↔ Q = ⊥ := by
  constructor
  · intro h
    ext p
    rw [show p ∈ (⊥ : AffineSubspace k P) ↔ False by rfl]
    have : p ∈ (Q : Set P) ↔ p ∈ (∅ : Set P) := by rw [h]
    simpa using this
  · intro h
    rw [h]
    rfl
