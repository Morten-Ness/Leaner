FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp
  | @cons a s ih =>
      by_cases h : a ∈ s
      · rw [Multiset.prod_cons, Multiset.toFinset_cons_of_mem h]
        rw [Finset.prod_insert]
        · rw [ih]
          simp [Multiset.count_cons, h, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        · simpa using h
      · rw [Multiset.prod_cons, Multiset.toFinset_cons_of_not_mem h]
        rw [Finset.prod_insert]
        · rw [ih]
          simp [Multiset.count_cons, h, pow_succ, mul_comm, mul_left_comm, mul_assoc]
        · simp [h]
