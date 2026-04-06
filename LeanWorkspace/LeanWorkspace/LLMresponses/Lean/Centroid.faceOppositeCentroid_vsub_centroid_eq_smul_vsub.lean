import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_vsub_centroid_eq_smul_vsub [CharZero k]
    (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i -ᵥ s.centroid = (n : k)⁻¹ • (s.centroid -ᵥ s.points i) := by
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    s.faceOppositeCentroid_vsub_centroid_eq_smul_vsub i
