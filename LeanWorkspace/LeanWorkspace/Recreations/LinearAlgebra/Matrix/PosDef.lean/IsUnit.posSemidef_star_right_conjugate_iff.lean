import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable [DecidableEq n] {U x : Matrix n n R}

theorem IsUnit.posSemidef_star_right_conjugate_iff (hU : IsUnit U) :
    Matrix.PosSemidef (U * x * star U) ↔ x.PosSemidef := by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

