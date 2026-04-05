import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [Fintype n]

theorem dotProduct_eq_zero_iff {v : n → R} : (∀ w, v ⬝ᵥ w = 0) ↔ v = 0 := ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

