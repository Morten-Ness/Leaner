FAIL
import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a' ≠ a, a' ∈ s → a' = 1) :
    s.prod = a ^ s.count a := by
  classical
  revert h
  induction s using Multiset.induction_on with
  | empty =>
      intro h
      simp
  | @cons b s ih =>
      intro h
      by_cases hba : b = a
      · subst hba
        have hs : ∀ a' ≠ a, a' ∈ s → a' = 1 := by
          intro a' ha' haMem
          exact h a' ha' (by simp [haMem])
        rw [Multiset.prod_cons, Multiset.count_cons_self]
        rw [ih hs]
        simp [pow_succ, mul_comm]
      · have hb1 : b = 1 := h b hba (by simp)
        have hs : ∀ a' ≠ a, a' ∈ s → a' = 1 := by
          intro a' ha' haMem
          exact h a' ha' (by simp [haMem])
        rw [Multiset.prod_cons, hb1, one_mul]
        rw [ih hs]
        rw [Multiset.count_cons_of_ne hba]
