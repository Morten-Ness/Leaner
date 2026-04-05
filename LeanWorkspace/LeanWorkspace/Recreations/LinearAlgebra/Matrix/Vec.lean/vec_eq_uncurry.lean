import Mathlib

theorem vec_eq_uncurry (A : Matrix m n R) : Matrix.vec A = Function.uncurry fun i j => A j i := rfl

