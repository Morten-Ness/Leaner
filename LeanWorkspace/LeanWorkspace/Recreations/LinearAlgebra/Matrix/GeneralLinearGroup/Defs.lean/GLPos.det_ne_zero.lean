import Mathlib

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem GLPos.det_ne_zero (A : Matrix.GLPos n R) : ((A : GL n R) : Matrix n n R).det ≠ 0 := ne_of_gt A.prop

