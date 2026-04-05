import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

omit [Fintype n] [Fintype m] in variable [Finite n] [Finite m] in
theorem posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n → R) :
    (vecMulVec a (star a)).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, Matrix.posSemidef_self_mul_conjTranspose]

