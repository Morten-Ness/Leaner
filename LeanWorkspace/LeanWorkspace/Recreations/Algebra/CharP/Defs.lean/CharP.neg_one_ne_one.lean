import Mathlib

variable (R : Type*)

theorem CharP.neg_one_ne_one [AddGroupWithOne R] (p : ℕ) [CharP R p] [Fact (2 < p)] :
    (-1 : R) ≠ (1 : R) := by
  rw [ne_comm, ← sub_ne_zero, sub_neg_eq_add, one_add_one_eq_two, ← Nat.cast_two, Ne,
    CharP.cast_eq_zero_iff R p 2]
  exact fun h ↦ (Fact.out : 2 < p).not_ge <| Nat.le_of_dvd Nat.zero_lt_two h

