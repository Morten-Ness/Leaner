import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_apply [DecidableEq n] {j' : n} :
    Matrix.updateCol M j c i j' = if j' = j then c i else M i j' := by
  by_cases h : j' = j
  · rw [h, Matrix.updateCol_self, if_pos rfl]
  · rw [Matrix.updateCol_ne h, if_neg h]

