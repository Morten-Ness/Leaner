import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

omit [Fintype m] in variable [Finite m] in
theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    Matrix.PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Aᴴ

