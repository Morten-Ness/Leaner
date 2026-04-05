import Mathlib

open scoped Topology

variable {K : Type*} (v : K) [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem convs_succ (n : ℕ) :
    (of v).convs (n + 1) = ⌊v⌋ + 1 / (of (Int.fract v)⁻¹).convs n := by
  rw [GenContFract.of_convs_eq_convs', convs'_succ, GenContFract.of_convs_eq_convs']

