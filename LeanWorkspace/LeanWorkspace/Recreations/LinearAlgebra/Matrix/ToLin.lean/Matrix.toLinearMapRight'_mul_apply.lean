import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

variable [DecidableEq m]

theorem Matrix.toLinearMapRight'_mul_apply [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) (x) :
    (M * N).toLinearMapRight' x = N.toLinearMapRight' (M.toLinearMapRight' x) := (vecMul_vecMul _ M N).symm

