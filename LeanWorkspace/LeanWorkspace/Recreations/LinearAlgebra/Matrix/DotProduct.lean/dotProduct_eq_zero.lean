import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [Fintype n]

theorem dotProduct_eq_zero (v : n → R) (h : ∀ w, v ⬝ᵥ w = 0) : v = 0 := dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

