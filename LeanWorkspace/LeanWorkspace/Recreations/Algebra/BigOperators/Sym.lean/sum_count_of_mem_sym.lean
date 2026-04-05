import Mathlib

theorem sum_count_of_mem_sym {α} [DecidableEq α] {m : ℕ} {k : Sym α m} {s : Finset α}
    (hk : k ∈ s.sym m) : (∑ i ∈ s, count i k) = m := by
  simp_all

