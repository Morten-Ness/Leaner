import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

theorem smul_centroid_vsub_point_eq_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    ((n : k) + 1) • (s.centroid -ᵥ s.points i) = ∑ x, (s.points x -ᵥ s.points i) := by
  rw [Affine.Simplex.centroid_eq_smul_sum_vsub_vadd s i, vadd_vsub, smul_smul, mul_inv_cancel₀, one_smul]
  norm_cast

