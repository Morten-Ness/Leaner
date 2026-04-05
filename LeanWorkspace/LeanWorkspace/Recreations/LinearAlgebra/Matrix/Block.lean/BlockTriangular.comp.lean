import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.comp [Zero R] {M : Matrix m m (Matrix n n R)} (h : Matrix.BlockTriangular M b) :
    Matrix.BlockTriangular (M.comp m m n n R) fun i ↦ b i.1 := fun i j lt ↦ by simp [h lt]

