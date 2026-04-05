import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

