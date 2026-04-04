import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem faceOppositeCentroid_mem_median (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.faceOppositeCentroid i ∈ s.median i := by
  simp [Affine.Simplex.median, right_mem_affineSpan_pair]

