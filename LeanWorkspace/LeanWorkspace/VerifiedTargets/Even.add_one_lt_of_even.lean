import Mathlib

variable {m n : ℕ}

theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by grind

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : ℕ) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, parity_simps]

example : ¬Even 25394535 := by decide

