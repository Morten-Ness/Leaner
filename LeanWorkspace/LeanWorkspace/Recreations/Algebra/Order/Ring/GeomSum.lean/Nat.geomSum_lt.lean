import Mathlib

variable {R : Type*}

variable {m n : ℕ} {s : Finset ℕ}

theorem Nat.geomSum_lt (hm : 2 ≤ m) (hs : ∀ k ∈ s, k < n) : ∑ k ∈ s, m ^ k < m ^ n := calc
    ∑ k ∈ s, m ^ k ≤ ∑ k ∈ range n, m ^ k := sum_le_sum_of_subset fun _ hk ↦
      mem_range.2 <| hs _ hk
    _ = (m ^ n - 1) / (m - 1) := Nat.geomSum_eq hm _
    _ ≤ m ^ n - 1 := Nat.div_le_self _ _
    _ < m ^ n := tsub_lt_self (Nat.pow_pos <| by lia) (by lia)

