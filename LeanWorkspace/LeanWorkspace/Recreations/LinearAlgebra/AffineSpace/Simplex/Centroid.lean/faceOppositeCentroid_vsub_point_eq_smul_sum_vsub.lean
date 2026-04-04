import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_point_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ (s.points i) = (n : k)⁻¹ • ∑ x, (s.points x -ᵥ s.points i) := by
  rw [Affine.Simplex.faceOppositeCentroid_eq_affineCombination,
    affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ ?_ (s.points i)]
  · simp only [weightedVSubOfPoint_apply, vadd_vsub]
    have h (i : Fin (n + 1)) : ∑ j ∈ {i}ᶜ, (n : k)⁻¹ • (s.points j -ᵥ s.points i) =
      ∑ j : (Fin (n + 1)), ((n : k)⁻¹ • (s.points j -ᵥ s.points i)) := by
      rw [← Finset.sum_compl_add_sum {i}]
      simp
    rw [h i, smul_sum]
  · simp only [sum_const, card_compl, Fintype.card_fin, card_singleton, add_tsub_cancel_right,
      nsmul_eq_mul]
    rw [mul_inv_cancel₀ (NeZero.ne (n : k))]

