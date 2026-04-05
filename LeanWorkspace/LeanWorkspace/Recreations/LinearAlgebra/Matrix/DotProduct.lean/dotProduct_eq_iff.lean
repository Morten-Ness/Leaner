import Mathlib

variable {m n p R : Type*}

variable [Semiring R] [Fintype n]

theorem dotProduct_eq_iff {v w : n → R} : (∀ u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w := ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

