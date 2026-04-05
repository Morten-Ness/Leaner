import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.toLinAlgEquiv'_one : Matrix.toLinAlgEquiv' (1 : Matrix n n R) = LinearMap.id := Matrix.toLin'_one

