import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  simp [not_disjoint_iff_nonempty_inter, Set.mem_div, div_eq_one, Set.Nonempty]

