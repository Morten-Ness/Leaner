import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

omit [Fintype m] in variable [Finite m] in
theorem conjTranspose_mul_mul_same {A : Matrix n n R} (hA : Matrix.PosSemidef A) (B : Matrix n m R) :
    Matrix.PosSemidef (Bᴴ * A * B) := by
  have := Fintype.ofFinite m
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x ↦ ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      Matrix.PosSemidef.dotProduct_mulVec_nonneg hA (B *ᵥ x)

