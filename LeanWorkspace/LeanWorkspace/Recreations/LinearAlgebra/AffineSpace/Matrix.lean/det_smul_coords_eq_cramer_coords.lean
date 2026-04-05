import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]

variable (b b₂ : AffineBasis ι k P)

theorem det_smul_coords_eq_cramer_coords (x : P) :
    (b.toMatrix b₂).det • b₂.coords x = (b.toMatrix b₂)ᵀ.cramer (b.coords x) := by
  have hu := AffineBasis.isUnit_toMatrix b b₂
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  rw [← AffineBasis.toMatrix_inv_vecMul_toMatrix b, Matrix.det_smul_inv_vecMul_eq_cramer_transpose _ _ hu]

