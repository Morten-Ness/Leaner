FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem median_eq_line_point_centroid [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.median i = line[k, s.points i, s.centroid] := by
  simp [Affine.Simplex.median, Affine.Simplex.faceOppositeCentroid, Affine.Simplex.centroid]
