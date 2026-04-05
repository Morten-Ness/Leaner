import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

theorem det_scalar (u : Rˣ) : Matrix.GeneralLinearGroup.det (Matrix.scalar n u) = u ^ Fintype.card n := by
  ext
  simp

