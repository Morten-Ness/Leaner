import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

theorem span_empty : affineSpan k (∅ : Set P) = ⊥ := (AffineSubspace.gi k V P).gc.l_bot

