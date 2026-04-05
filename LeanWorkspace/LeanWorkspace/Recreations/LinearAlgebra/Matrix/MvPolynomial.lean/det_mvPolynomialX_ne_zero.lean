import Mathlib

variable {m n R S : Type*}

theorem det_mvPolynomialX_ne_zero [DecidableEq m] [Fintype m] [CommRing R] [Nontrivial R] :
    det (Matrix.mvPolynomialX m m R) ≠ 0 := by
  intro h_det
  have := congr_arg Matrix.det (Matrix.mvPolynomialX_mapMatrix_eval (1 : Matrix m m R))
  rw [det_one, ← RingHom.map_det, h_det, map_zero] at this
  exact zero_ne_one this

