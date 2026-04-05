import Mathlib

open scoped Finset

variable {α : Type*} [DecidableEq α]

theorem toFinset_card_eq_one_iff (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

