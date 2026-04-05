import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_smul_left (M : Matrix n n R) (j : n) (s : R) (u : n → R) :
    Matrix.det (updateRow (s • M) j u) = s ^ (Fintype.card n - 1) * Matrix.det (updateRow M j u) := MultilinearMap.map_update_smul_left _ M j s u

