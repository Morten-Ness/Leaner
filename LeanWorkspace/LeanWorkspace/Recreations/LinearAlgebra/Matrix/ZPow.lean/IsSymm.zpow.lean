import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem IsSymm.zpow {A : M} (h : A.IsSymm) (k : ℤ) :
    (A ^ k).IsSymm := by
  rw [Matrix.IsSymm, Matrix.transpose_zpow, h]

