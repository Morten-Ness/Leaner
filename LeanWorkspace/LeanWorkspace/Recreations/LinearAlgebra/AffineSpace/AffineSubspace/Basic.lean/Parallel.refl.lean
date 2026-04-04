import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem Parallel.refl (s : AffineSubspace k P) : s ∥ s := ⟨0, by simp⟩

