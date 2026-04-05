import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_conjTranspose [DecidableEq m] [Star α] :
    Matrix.updateCol Mᴴ i (star b) = (Matrix.updateRow M i b)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, Matrix.updateCol_transpose,
    Matrix.map_updateRow]
  rfl

