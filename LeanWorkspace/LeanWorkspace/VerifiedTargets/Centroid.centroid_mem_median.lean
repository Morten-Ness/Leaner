import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_mem_median [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid ∈ s.median i := by
  rw [Affine.Simplex.median]
  have h : s.centroid = ((n : k) * (1 / (n + 1))) • (s.faceOppositeCentroid i -ᵥ s.points i)
    +ᵥ s.points i := by
    rw [eq_vadd_iff_vsub_eq, Affine.Simplex.centroid_vsub_point_eq_smul_vsub,
      Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_vsub, smul_smul, one_div, mul_assoc,
      inv_mul_cancel₀ (by norm_cast), mul_one]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

