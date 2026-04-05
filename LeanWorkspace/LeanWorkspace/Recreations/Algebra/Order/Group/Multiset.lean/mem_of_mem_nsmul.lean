import Mathlib

variable {α β : Type*}

theorem mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s := by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul, mem_add] at h
    exact h.elim ih id

