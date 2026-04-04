import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_faceOppositeCentroid [CharZero k] (s : Affine.Simplex k P n)
    (i j : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.faceOppositeCentroid j =
    (n : k)⁻¹ • (s.points j -ᵥ s.points i) := by
  rw [Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd s i, Affine.Simplex.faceOppositeCentroid_eq_sum_vsub_vadd s j,
    vadd_vsub_vadd_comm _ _ (s.points i) (s.points j)]
  have h1 (i : Fin (n + 1)) : ∑ x, (s.points x -ᵥ s.points i) =
      ∑ x, (s.points x -ᵥ s.points 0 - (s.points i-ᵥ s.points 0)) := by
    apply sum_congr rfl
    simp
  simp_rw [h1 i, h1 j, sum_sub_distrib]
  rw [smul_sub, smul_sub, sub_sub_sub_cancel_left, ← smul_sub, ← sum_sub_distrib,
    vsub_sub_vsub_cancel_right, sum_const, card_univ, Fintype.card_fin]
  have : (s.points i -ᵥ s.points j) = -(s.points j -ᵥ s.points i) := by simp
  rw [this, ← sub_eq_add_neg, add_smul, sub_eq_iff_eq_add , one_smul, smul_add, add_comm]
  have : (n : k)⁻¹ • n • (s.points j -ᵥ s.points i) =
      (n : k)⁻¹ • (n : k) • (s.points j -ᵥ s.points i) := by
    norm_cast0
    congr 1
  rw [this, smul_smul, inv_eq_one_div, one_div_mul_cancel (NeZero.ne (n : k)), one_smul]

