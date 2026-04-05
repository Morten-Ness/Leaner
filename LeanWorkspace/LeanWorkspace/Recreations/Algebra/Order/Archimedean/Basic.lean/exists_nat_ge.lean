import Mathlib

variable {G M R K : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem exists_nat_ge (x : R) :
    ∃ n : ℕ, x ≤ n := by
  nontriviality R
  exact (Archimedean.arch x one_pos).imp fun n h => by rwa [← nsmul_one]

