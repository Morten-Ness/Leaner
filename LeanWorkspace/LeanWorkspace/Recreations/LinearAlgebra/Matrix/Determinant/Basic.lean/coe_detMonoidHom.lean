import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem coe_detMonoidHom : (Matrix.detMonoidHom : Matrix n n R → R) = Matrix.det := rfl

