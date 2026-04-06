import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_vsub_centroid_eq_smul_vsub [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i -ᵥ s.centroid = (n : k) • (s.centroid -ᵥ s.faceOppositeCentroid i) := by
  simpa using Affine.Simplex.point_vsub_centroid_eq_smul_vsub (s := s) (i := i)
