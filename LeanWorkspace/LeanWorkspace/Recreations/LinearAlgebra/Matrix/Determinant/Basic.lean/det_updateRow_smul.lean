import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_smul (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    Matrix.det (updateRow M j <| s • u) = s * Matrix.det (updateRow M j u) := (Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_update_smul M j s u

