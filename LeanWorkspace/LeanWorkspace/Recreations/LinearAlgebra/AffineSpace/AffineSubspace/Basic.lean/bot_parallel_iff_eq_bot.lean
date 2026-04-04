import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem bot_parallel_iff_eq_bot {s : AffineSubspace k P} : ⊥ ∥ s ↔ s = ⊥ := by
  rw [AffineSubspace.parallel_comm, AffineSubspace.parallel_bot_iff_eq_bot]

