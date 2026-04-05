import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  symm
  rw [← vsub_sub_vsub_cancel_right _ _ (s.points i),
    Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub,
    Affine.Simplex.centroid_vsub_eq, ← neg_vsub_eq_vsub_rev,
    Affine.Simplex.centroid_vsub_eq, ← sub_smul, smul_smul, ← neg_smul]
  congr
  simp_rw [mul_sub, sub_eq_iff_eq_add, neg_add_eq_sub]
  symm
  rw [sub_eq_iff_eq_add, mul_inv_cancel₀ (NeZero.ne (n : k))]
  have : (↑n + (1 : k))⁻¹ = 1 * (↑n + (1 : k))⁻¹ := by simp
  nth_rw 2 [this]
  rw [← add_mul, mul_inv_cancel₀ (by norm_cast)]

