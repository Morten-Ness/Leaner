import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem map_updateCol [DecidableEq n] (f : α → β) :
    map (Matrix.updateCol M j c) f = Matrix.updateCol (M.map f) j (f ∘ c) := by
  ext
  rw [Matrix.updateCol_apply, map_apply, map_apply, Matrix.updateCol_apply]
  exact apply_ite f _ _ _

