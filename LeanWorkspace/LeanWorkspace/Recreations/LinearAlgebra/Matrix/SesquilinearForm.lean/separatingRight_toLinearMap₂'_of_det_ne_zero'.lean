import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable [IsDomain R] {M : Matrix n n R}

variable [DecidableEq m]

theorem separatingRight_toLinearMap₂'_of_det_ne_zero' (h : M.det ≠ 0) :
    (Matrix.toLinearMap₂' R M).SeparatingRight (R := R) :=
  LinearMap.separatingRight_toLinearMap₂'_iff_det_ne_zero.mpr h

