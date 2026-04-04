import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {s : Set P}

theorem bot_lt_affineSpan : ⊥ < affineSpan k s ↔ s.Nonempty := by
  rw [bot_lt_iff_ne_bot, nonempty_iff_ne_empty]
  exact (affineSpan_eq_bot _).not

