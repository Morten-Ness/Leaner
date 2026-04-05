import Mathlib

variable {G M R K : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

theorem pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : R) (hy1 : 1 < y) : ∃ n : ℕ, x < y ^ n := by
  obtain ⟨z, hz, rfl⟩ := exists_pos_add_of_lt' hy1
  rw [add_comm]
  exact add_one_pow_unbounded_of_pos _ hz

