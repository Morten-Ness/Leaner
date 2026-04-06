import Mathlib

variable {m n : ℕ}

theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by
  rcases hn with ⟨a, rfl⟩
  rcases hm with ⟨b, rfl⟩
  omega
