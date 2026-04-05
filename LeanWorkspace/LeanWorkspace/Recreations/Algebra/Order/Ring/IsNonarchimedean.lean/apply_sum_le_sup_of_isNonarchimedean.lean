import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

omit [Semiring R] in
theorem apply_sum_le_sup_of_isNonarchimedean {α β : Type*} [AddCommMonoid α] {f : α → R}
    (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempty : s.Nonempty) {l : β → α} :
    f (∑ i ∈ s, l i) ≤ s.sup' hnonempty fun i => f (l i) := by
  induction hnonempty using Nonempty.cons_induction with
  | singleton i => simp
  | cons i s _ hs hind =>
    simp only [sum_cons, le_sup'_iff, mem_cons, exists_eq_or_imp]
    rw [← le_sup'_iff hs]
    rcases le_max_iff.mp <| nonarch (l i) (∑ i ∈ s, l i) with h₁ | h₂
    · exact .inl h₁
    · exact .inr <| le_trans h₂ hind

