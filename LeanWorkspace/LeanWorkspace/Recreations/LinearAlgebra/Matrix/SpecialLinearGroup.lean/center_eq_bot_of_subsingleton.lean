import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem center_eq_bot_of_subsingleton [Subsingleton n] :
    center (Matrix.SpecialLinearGroup n R) = ⊥ := eq_bot_iff.mpr fun x _ ↦ by rw [mem_bot, Subsingleton.elim x 1]

