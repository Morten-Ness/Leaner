import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

omit [Fintype n] in variable [Finite n] in
theorem posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n → R) :
    (vecMulVec (star a) a).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, Matrix.posSemidef_conjTranspose_mul_self]

