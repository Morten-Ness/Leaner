import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

variable [Zero R]

theorem blockTriangular_zero : Matrix.BlockTriangular (0 : Matrix m m R) b := fun _ _ _ => rfl

