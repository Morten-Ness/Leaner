import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

theorem Matrix.coe_vecMulLinear [Fintype m] (M : Matrix m n R) :
    (M.vecMulLinear : _ → _) = M.vecMul := rfl

