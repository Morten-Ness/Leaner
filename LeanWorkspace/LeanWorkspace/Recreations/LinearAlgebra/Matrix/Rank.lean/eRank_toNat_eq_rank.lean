import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem eRank_toNat_eq_rank (A : Matrix m n R) : A.eRank.toNat = A.rank := by
  rw [Matrix.eRank_toNat_eq_finrank, ← Matrix.rank_eq_finrank_span_cols]

