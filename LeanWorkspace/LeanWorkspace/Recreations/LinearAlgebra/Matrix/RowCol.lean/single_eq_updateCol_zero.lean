import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem single_eq_updateCol_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = Matrix.updateCol 0 j (Pi.single i r) := by
  simpa [← Matrix.updateCol_transpose] using congr($(Matrix.single_eq_updateRow_zero j i r)ᵀ)

