import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_point_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.points i =
    (n + 1 : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) := by
  rw [← vsub_sub_vsub_cancel_right _ (s.centroid) (s.points i),
    Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, Affine.Simplex.centroid_vsub_eq,
    ← sub_smul, smul_smul]
  congr
  rw [mul_sub, add_mul, mul_inv_cancel₀ (NeZero.ne (n : k)), mul_inv_cancel₀ (by norm_cast),
    one_mul]
  grind

