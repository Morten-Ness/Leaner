import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem exists_pos_rat_lt {x : K} (x0 : 0 < x) : ∃ q : ℚ, 0 < q ∧ (q : K) < x := by
  simpa only [Rat.cast_pos] using exists_rat_btwn x0

