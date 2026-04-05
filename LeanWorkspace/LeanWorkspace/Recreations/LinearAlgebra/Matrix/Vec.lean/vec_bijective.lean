import Mathlib

theorem vec_bijective : Function.Bijective (Matrix.vec : Matrix m n R → _) := Equiv.curry _ _ _ |>.symm.bijective.comp Function.swap_bijective

