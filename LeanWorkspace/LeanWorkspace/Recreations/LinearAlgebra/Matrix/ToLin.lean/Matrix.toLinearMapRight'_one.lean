import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

variable [DecidableEq m]

theorem Matrix.toLinearMapRight'_one :
    (1 : Matrix m m R).toLinearMapRight' = LinearMap.id := by
  ext
  simp

