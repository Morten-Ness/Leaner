import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_conjTranspose [DecidableEq n] [Star α] :
    Matrix.updateRow Mᴴ j (star c) = (Matrix.updateCol M j c)ᴴ := by
  rw [conjTranspose, conjTranspose, transpose_map, transpose_map, Matrix.updateRow_transpose,
    Matrix.map_updateCol]
  rfl

