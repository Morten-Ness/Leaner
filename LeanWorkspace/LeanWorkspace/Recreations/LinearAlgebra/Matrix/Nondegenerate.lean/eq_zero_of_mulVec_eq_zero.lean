import Mathlib

variable {m n R A : Type*} [CommRing R] [Fintype m] [Fintype n] [CommRing A] [IsDomain A]
  {M : Matrix m n R}

variable [DecidableEq m] {M : Matrix m m A}

theorem eq_zero_of_mulVec_eq_zero (hM : M.det ≠ 0) {v : m → A}
    (hv : M *ᵥ v = 0) : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero (by rwa [det_transpose]) ((vecMul_transpose M v).trans hv)

