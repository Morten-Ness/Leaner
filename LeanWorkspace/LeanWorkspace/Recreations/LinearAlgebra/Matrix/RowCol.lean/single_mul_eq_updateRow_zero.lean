import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem single_mul_eq_updateRow_zero
    [DecidableEq l] [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring α]
    (i : l) (j : m) (r : α) (B : Matrix m n α) :
    single i j r * B = Matrix.updateRow 0 i (r • B.row j) := by
  rw [Matrix.single_eq_updateRow_zero, Matrix.updateRow_mul, Matrix.zero_mul, single_vecMul]

