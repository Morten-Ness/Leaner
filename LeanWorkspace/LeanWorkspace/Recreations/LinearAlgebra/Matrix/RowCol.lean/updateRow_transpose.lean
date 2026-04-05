import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_transpose [DecidableEq n] : Matrix.updateRow Mᵀ j c = (Matrix.updateCol M j c)ᵀ := by
  ext
  rw [transpose_apply, Matrix.updateRow_apply, Matrix.updateCol_apply]
  rfl

