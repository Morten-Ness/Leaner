import Mathlib

variable {G M R K : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

theorem exists_nat_gt (x : R) : ∃ n : ℕ, x < n := (exists_lt_nsmul zero_lt_one x).imp fun n hn ↦ by rwa [← nsmul_one]

