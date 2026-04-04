import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem nonempty_iff_ne_bot (Q : AffineSubspace k P) : (Q : Set P).Nonempty ↔ Q ≠ ⊥ := by
  rw [nonempty_iff_ne_empty]
  exact not_congr Q.coe_eq_bot_iff

