import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_vsub_faceOppositeCentroid_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • (s.points i -ᵥ s.centroid) := by
  rw [Affine.Simplex.point_vsub_centroid_eq_smul_vsub, smul_smul, inv_mul_cancel₀ (NeZero.ne (n : k)), one_smul]

