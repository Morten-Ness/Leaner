import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

variable [DecidableEq m]

theorem LinearMap.toMatrixRight'_comp [Fintype l] [DecidableEq l] (f : (l → R) →ₗ[R] m → R)
    (g : (m → R) →ₗ[R] n → R) : (g ∘ₗ f).toMatrixRight' = f.toMatrixRight' * g.toMatrixRight' := Matrix.toLinearMapRight'.injective <| by simp

