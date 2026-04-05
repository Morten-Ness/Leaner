import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.neg [NegZeroClass R] {M : Matrix m m R}
    (hM : Matrix.BlockTriangular M b) : Matrix.BlockTriangular (-M) b := fun _ _ h => by rw [neg_apply, hM h, neg_zero]

