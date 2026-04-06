FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem centroid_mem_median [CharZero k] (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.centroid ∈ s.median i := by
  simpa [Affine.Simplex.centroid, Affine.Simplex.median, Set.mem_image, exists_prop] using
    (Affine.Simplex.range_weightedVSub_vadd_eq_zero (s := s) i)
