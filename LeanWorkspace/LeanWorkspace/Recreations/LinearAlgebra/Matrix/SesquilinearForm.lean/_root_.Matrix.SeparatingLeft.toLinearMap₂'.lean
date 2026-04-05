import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable {B : (m → R) →ₗ[R] (n → R) →ₗ[R] R}

theorem _root_.Matrix.SeparatingLeft.toLinearMap₂' (h : M.SeparatingLeft) :
    (toLinearMap₂' R M).SeparatingLeft (R := R) := by
  simpa [SeparatingLeft, toLinearMap₂'_apply', separatingLeft_def] using h

