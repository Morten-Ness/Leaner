import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem two_dvd_mul_sub_one (k : ℕ) : 2 ∣ k * (k - 1) := by
  rcases k with rfl | k; · simp
  simpa [mul_comm (k + 1)] using Nat.two_dvd_mul_add_one k

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp [*, parity_simps]

example : ¬Even 25394535 := by decide

