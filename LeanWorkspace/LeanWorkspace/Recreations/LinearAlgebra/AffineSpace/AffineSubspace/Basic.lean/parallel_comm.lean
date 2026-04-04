import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem parallel_comm {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔ s₂ ∥ s₁ := ⟨AffineSubspace.Parallel.symm, AffineSubspace.Parallel.symm⟩

