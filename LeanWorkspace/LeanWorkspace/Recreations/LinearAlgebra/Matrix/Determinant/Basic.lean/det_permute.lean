import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_permute (σ : Perm n) (M : Matrix n n R) :
    (M.submatrix σ id).det = Perm.sign σ * M.det := ((Matrix.detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).map_perm M σ).trans (by simp [Units.smul_def, Matrix.det])

