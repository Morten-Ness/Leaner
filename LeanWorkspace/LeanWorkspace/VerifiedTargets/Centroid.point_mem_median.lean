import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {n : ℕ}

variable [NeZero n]

theorem point_mem_median (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.median i := by
  simp [Affine.Simplex.median, left_mem_affineSpan_pair]

