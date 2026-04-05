import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable [DecidableEq n] {U x : Matrix n n R}

theorem IsUnit.posSemidef_star_left_conjugate_iff (hU : IsUnit U) :
    Matrix.PosSemidef (star U * x * U) ↔ x.PosSemidef := by
  refine ⟨fun h ↦ ?_, fun h ↦ Matrix.PosSemidef.conjTranspose_mul_mul_same h _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := Matrix.PosSemidef.conjTranspose_mul_mul_same h ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

