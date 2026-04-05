import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add [AddZeroClass R] (hM : Matrix.BlockTriangular M b) (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M + N) b := fun i j h => by simp_rw [Matrix.add_apply, hM h, hN h, zero_add]

