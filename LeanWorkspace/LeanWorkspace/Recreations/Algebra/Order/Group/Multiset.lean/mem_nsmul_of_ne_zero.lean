import Mathlib

variable {α β : Type*}

theorem mem_nsmul_of_ne_zero {a : α} {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s := by
  simp [*]

