FAIL
import Mathlib

variable {ι M M₀ R : Type*}

variable [NonUnitalNonAssocSemiring R] (s : Multiset R)

theorem multiset_sum_left (b : R) (h : ∀ a ∈ s, Commute a b) : Commute s.sum b := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      exact Commute.zero_left b
  | @cons a s ih =>
      rw [Multiset.sum_cons]
      have ha : Commute a b := h a (by simp)
      have hs : ∀ x ∈ s, Commute x b := by
        intro x hx
        exact h x (by simp [hx])
      have hs_sum : Commute s.sum b := ih hs
      exact hs_sum.add_left ha
