import Mathlib

variable {M N P σ : Type*}

variable [MulOne M] [MulOne N] [Mul P] (S : Subsemigroup M)

theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ := by
  ext x
  simp [Subsemigroup.mem_map]
