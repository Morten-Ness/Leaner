import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem median_eq_line_point_centroid [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.median i = line[k, s.points i, s.centroid] := by
  have h1 : s.median i ≤ line[k, s.points i, s.centroid] := by
    unfold Affine.Simplex.median
    apply affineSpan_pair_le_of_right_mem
    rw [Affine.Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point]
    have h : (n : k)⁻¹ • (s.centroid -ᵥ s.points i) = (-1 / n : k) • (s.points i -ᵥ s.centroid)
        := by
      rw [← neg_vsub_eq_vsub_rev]
      have : -(s.points i -ᵥ s.centroid) = (-1 : k) • (s.points i -ᵥ s.centroid) := by simp
      rw [this, smul_smul]
      congr 1
      rw [mul_neg_one, inv_eq_one_div, neg_div]
    rw [h]
    exact smul_vsub_rev_vadd_mem_affineSpan_pair _ _ _
  have h2 : line[k, s.points i, s.centroid] ≤ s.median i := by
    rw [Affine.Simplex.median]
    apply affineSpan_pair_le_of_right_mem
    exact Affine.Simplex.centroid_mem_median s i
  exact le_antisymm h1 h2

