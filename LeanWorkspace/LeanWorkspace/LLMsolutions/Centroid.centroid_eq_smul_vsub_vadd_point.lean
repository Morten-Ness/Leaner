FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_eq_smul_vsub_vadd_point [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid = (n : k) • (s.faceOppositeCentroid i -ᵥ s.centroid) +ᵥ s.points i := by
  classical
  rw [eq_comm]
  refine eq_of_vsub_eq_vsub_right ?p (s.points i)
  rw [vsub_vadd, vsub_vadd]
  simpa using s.centroid_vsub_point_eq_inv_card_smul_sum_vsub (s.points i)
