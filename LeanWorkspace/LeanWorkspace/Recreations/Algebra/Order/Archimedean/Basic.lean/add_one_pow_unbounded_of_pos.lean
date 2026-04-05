import Mathlib

variable {G M R K : Type*}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [Archimedean R] {y : R}

theorem add_one_pow_unbounded_of_pos (x : R) (hy : 0 < y) : ∃ n : ℕ, x < (y + 1) ^ n := have : 0 ≤ 1 + y := add_nonneg zero_le_one hy.le
  (Archimedean.arch x hy).imp fun n h ↦
    calc
      x ≤ n • y := h
      _ = n * y := nsmul_eq_mul _ _
      _ < 1 + n * y := lt_one_add _
      _ ≤ (1 + y) ^ n :=
        one_add_mul_le_pow_of_sq_nonneg (pow_nonneg hy.le _) (pow_nonneg this _)
          (add_nonneg zero_le_two hy.le) _
      _ = (y + 1) ^ n := by rw [add_comm]

