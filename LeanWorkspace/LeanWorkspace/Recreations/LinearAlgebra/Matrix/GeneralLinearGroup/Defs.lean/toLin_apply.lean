import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v}

variable [CommRing R]

variable (A B : GL n R)

theorem toLin_apply (v : n → R) : (Matrix.GeneralLinearGroup.toLin A : _ → n → R) v = Matrix.mulVecLin A v := rfl

