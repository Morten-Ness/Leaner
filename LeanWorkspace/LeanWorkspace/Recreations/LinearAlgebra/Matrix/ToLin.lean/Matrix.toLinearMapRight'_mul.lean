import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

variable [DecidableEq m]

theorem Matrix.toLinearMapRight'_mul [Fintype l] [DecidableEq l] (M : Matrix l m R)
    (N : Matrix m n R) :
    (M * N).toLinearMapRight' = N.toLinearMapRight' ∘ₗ M.toLinearMapRight' := LinearMap.ext fun _x ↦ (vecMul_vecMul _ M N).symm

