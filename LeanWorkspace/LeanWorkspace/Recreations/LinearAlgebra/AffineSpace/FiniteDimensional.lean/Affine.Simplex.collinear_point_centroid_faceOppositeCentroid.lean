import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

variable (k)

theorem Affine.Simplex.collinear_point_centroid_faceOppositeCentroid [CharZero k] {n : ℕ} [NeZero n]
    (s : Simplex k P n) (i : Fin (n + 1)) :
    Collinear k {s.points i, s.centroid, s.faceOppositeCentroid i} := by
  apply collinear_insert_of_mem_affineSpan_pair
  have h : s.points i = (-n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.centroid := by
    rw [← neg_vsub_eq_vsub_rev, neg_smul_neg, ← point_vsub_centroid_eq_smul_vsub, vsub_vadd]
  rw [h]
  exact smul_vsub_vadd_mem_affineSpan_pair _ _ _

