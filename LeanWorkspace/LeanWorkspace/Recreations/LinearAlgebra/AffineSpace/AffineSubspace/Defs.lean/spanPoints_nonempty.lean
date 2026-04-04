import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem spanPoints_nonempty (s : Set P) : (spanPoints k s).Nonempty ↔ s.Nonempty := by
  constructor
  · contrapose
    rw [Set.not_nonempty_iff_eq_empty, Set.not_nonempty_iff_eq_empty]
    intro h
    simp [h, spanPoints]
  · exact fun h => h.mono (subset_spanPoints _ _)

