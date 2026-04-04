import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P) in

variable {P}

theorem direction_bot : (⊥ : AffineSubspace k P).direction = ⊥ := by
  rw [AffineSubspace.direction_eq_vectorSpan, AffineSubspace.bot_coe, vectorSpan_def, vsub_empty, Submodule.span_empty]

