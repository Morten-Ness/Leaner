import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem parallel_bot_iff_eq_bot {s : AffineSubspace k P} : s ∥ ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ AffineSubspace.Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, AffineSubspace.map_eq_bot_iff] at h

