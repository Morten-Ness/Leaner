import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem smul_faceOppositeCentroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    (n : k) • (s.faceOppositeCentroid i -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  simp [Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd, smul_smul, mul_inv_cancel₀ (NeZero.ne (n : k)),
    one_smul]

