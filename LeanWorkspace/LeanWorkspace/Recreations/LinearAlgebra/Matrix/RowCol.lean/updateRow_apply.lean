import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_apply [DecidableEq m] {i' : m} :
    Matrix.updateRow M i b i' j = if i' = i then b j else M i' j := by
  by_cases h : i' = i
  · rw [h, Matrix.updateRow_self, if_pos rfl]
  · rw [Matrix.updateRow_ne h, if_neg h]

