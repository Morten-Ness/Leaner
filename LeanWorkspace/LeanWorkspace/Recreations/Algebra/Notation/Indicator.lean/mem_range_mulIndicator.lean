import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (Set.mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [Set.mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

