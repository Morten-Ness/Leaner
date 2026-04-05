import Mathlib

variable {n : Type u} {R : Type v} [DecidableEq n] [Fintype n]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem mem_glpos (A : GL n R) : A ∈ Matrix.GLPos n R ↔ 0 < (Matrix.GeneralLinearGroup.det A : R) := Iff.rfl

