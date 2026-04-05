import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem cRank_zero {m n : Type*} [Nontrivial R] : Matrix.cRank (0 : Matrix m n R) = 0 := by
  obtain hn | hn := isEmpty_or_nonempty n
  · rw [Matrix.cRank, Set.range_eq_empty, span_empty, rank_bot]
  rw [Matrix.cRank, transpose_zero, range_zero, span_zero_singleton, rank_bot]

