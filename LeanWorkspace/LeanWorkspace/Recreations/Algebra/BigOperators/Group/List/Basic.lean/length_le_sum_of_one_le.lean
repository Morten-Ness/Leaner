import Mathlib

variable {ι α β M N P G : Type*}

theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum := by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons, length, add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

