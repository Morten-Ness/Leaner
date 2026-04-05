import Mathlib

variable {α β n m R : Type*}

theorem IsSymm.pow [CommSemiring α] [Fintype n] [DecidableEq n] {A : Matrix n n α} (h : A.IsSymm)
    (k : ℕ) :
    (A ^ k).IsSymm := by
  rw [Matrix.IsSymm, transpose_pow, h]

