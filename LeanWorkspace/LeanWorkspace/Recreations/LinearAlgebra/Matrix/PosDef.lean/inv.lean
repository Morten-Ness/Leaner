import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]

theorem inv [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : M⁻¹.PosDef := by
  have := Matrix.PosDef.mul_mul_conjTranspose_same hM (B := M⁻¹) ?_
  · let _ := Matrix.PosDef.isUnit hM.invertible
    simpa using Matrix.PosDef.conjTranspose this
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, Matrix.PosDef.isUnit hM]

