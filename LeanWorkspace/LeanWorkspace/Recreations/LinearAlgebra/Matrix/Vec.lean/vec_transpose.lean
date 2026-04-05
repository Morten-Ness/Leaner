import Mathlib

theorem vec_transpose (A : Matrix m n R) : Matrix.vec Aᵀ = Matrix.vec A ∘ Prod.swap := rfl

