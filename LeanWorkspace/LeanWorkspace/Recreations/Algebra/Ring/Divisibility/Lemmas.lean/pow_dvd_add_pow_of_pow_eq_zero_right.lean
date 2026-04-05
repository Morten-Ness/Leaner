import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Semiring R]

theorem pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p := by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij ↦ ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m ≤ i) | (hi : i + 1 ≤ m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by lia : n ≤ j) hy]

