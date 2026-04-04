import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {s : Set P}

theorem affineSpan_eq_top_iff_nonempty_of_subsingleton [Subsingleton P] :
    affineSpan k s = ⊤ ↔ s.Nonempty := by
  rw [← bot_lt_affineSpan k, IsSimpleOrder.bot_lt_iff_eq_top]

