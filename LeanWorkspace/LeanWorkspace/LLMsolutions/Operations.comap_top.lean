import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ := by
  ext x
  simp
