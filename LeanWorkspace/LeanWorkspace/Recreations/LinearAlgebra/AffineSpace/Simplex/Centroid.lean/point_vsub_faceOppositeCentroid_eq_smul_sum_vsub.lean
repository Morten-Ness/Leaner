import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_vsub_faceOppositeCentroid_eq_smul_sum_vsub [CharZero k] (s : Affine.Simplex k P n)
    (i : Fin (n + 1)) :
    s.points i -ᵥ s.faceOppositeCentroid i = (n : k)⁻¹ • ∑ x, (s.points i -ᵥ s.points x) := by
  rw [← neg_vsub_eq_vsub_rev, Affine.Simplex.faceOppositeCentroid_vsub_point_eq_smul_sum_vsub, ← neg_smul,
    Lean.Grind.Ring.neg_eq_mul_neg_one, ← smul_smul, smul_sum]
  simp only [neg_smul, one_smul, neg_vsub_eq_vsub_rev]

