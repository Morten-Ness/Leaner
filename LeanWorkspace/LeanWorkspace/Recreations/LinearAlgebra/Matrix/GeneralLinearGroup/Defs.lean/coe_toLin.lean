import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable (A B : GL n R)

theorem coe_toLin : (Matrix.GeneralLinearGroup.toLin A : (n → R) →ₗ[R] n → R) = Matrix.mulVecLin A := rfl

