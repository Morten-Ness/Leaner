import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem _root_.Odd.not_two_dvd_nat (h : Odd n) : ¬(2 ∣ n) := by grind

