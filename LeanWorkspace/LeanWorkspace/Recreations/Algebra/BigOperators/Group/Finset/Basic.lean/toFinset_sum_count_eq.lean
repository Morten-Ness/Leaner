import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι]

theorem toFinset_sum_count_eq (s : Multiset ι) : ∑ a ∈ s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : ℕ))).symm

