import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa using List.toFinset_sum_count_eq_length l
