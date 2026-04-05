import Mathlib

variable {α β : Type*}

variable (p : α → Prop) [DecidablePred p]

theorem filter_nsmul (s : Multiset α) (n : ℕ) : filter p (n • s) = n • filter p s := by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [Multiset.nsmul_cons, filter_add, ih, filter_cons, nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (Multiset.mem_of_mem_nsmul hb)]

