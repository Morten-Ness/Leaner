import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_eq_smul_vsub_vadd_point [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) +ᵥ s.centroid := by
  rw [Affine.Simplex.centroid_vsub_point_eq_smul_vsub, eq_vadd_iff_vsub_eq, smul_smul,
    inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

