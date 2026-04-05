import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

variable [DecidableEq m]

theorem Matrix.toLinearMapRight'_apply (M : Matrix m n R) (v : m → R) :
    M.toLinearMapRight' v = v ᵥ* M := rfl

