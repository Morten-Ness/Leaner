import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]

variable (b b₂ : AffineBasis ι k P)

theorem toMatrix_inv_vecMul_toMatrix (x : P) :
    b.coords x ᵥ* (b.toMatrix b₂)⁻¹ = b₂.coords x := by
  have hu := AffineBasis.isUnit_toMatrix b b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← AffineBasis.toMatrix_vecMul_coords b b₂, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu,
    Matrix.vecMul_one]

