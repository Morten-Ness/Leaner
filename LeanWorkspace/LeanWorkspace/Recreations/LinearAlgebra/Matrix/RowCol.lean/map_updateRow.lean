import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem map_updateRow [DecidableEq m] (f : α → β) :
    map (Matrix.updateRow M i b) f = Matrix.updateRow (M.map f) i (f ∘ b) := by
  ext
  rw [Matrix.updateRow_apply, map_apply, map_apply, Matrix.updateRow_apply]
  exact apply_ite f _ _ _

