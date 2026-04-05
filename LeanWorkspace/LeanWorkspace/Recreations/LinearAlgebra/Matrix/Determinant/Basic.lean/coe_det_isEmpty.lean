import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem coe_det_isEmpty [IsEmpty n] : (Matrix.det : Matrix n n R → R) = Function.const _ 1 := by
  ext
  exact Matrix.det_isEmpty

