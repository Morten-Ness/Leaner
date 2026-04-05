import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem mod_two_add_add_odd_mod_two (m : ℕ) {n : ℕ} (hn : Odd n) : m % 2 + (m + n) % 2 = 1 := by grind

