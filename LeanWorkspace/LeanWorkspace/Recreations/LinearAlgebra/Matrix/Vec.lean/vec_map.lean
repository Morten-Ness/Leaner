import Mathlib

theorem vec_map (A : Matrix m n R) (f : R → S) : Matrix.vec (A.map f) = f ∘ Matrix.vec A := rfl

