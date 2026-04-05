import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_conjTranspose [StarRing R] (M : Matrix m m R) : Matrix.det Mᴴ = star (Matrix.det M) := ((starRingEnd R).map_det _).symm.trans <| congr_arg star M.det_transpose

