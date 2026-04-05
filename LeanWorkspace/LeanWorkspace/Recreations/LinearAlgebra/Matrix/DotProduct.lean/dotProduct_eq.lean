import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [Fintype n]

theorem dotProduct_eq (v w : n → R) (h : ∀ u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

