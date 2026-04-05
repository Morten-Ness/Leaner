import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_add (M : Matrix n n R) (j : n) (u v : n → R) :
    Matrix.det (updateRow M j <| u + v) = Matrix.det (updateRow M j u) + Matrix.det (updateRow M j v) := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_add M j u v

