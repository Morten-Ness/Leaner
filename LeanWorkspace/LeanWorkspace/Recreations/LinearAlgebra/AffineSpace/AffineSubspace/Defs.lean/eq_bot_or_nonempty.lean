import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem eq_bot_or_nonempty (Q : AffineSubspace k P) : Q = ⊥ ∨ (Q : Set P).Nonempty := by
  rw [AffineSubspace.nonempty_iff_ne_bot]
  apply eq_or_ne

