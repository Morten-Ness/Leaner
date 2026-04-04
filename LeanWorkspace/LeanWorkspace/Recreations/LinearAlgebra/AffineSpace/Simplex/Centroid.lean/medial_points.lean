import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem medial_points [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.medial.points i = s.faceOppositeCentroid i := rfl

