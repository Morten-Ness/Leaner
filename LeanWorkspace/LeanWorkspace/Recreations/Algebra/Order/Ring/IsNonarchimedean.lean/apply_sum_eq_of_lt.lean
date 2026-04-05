import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

theorem apply_sum_eq_of_lt {α β F : Type*} [AddCommGroup α] [FunLike F α R]
    [AddGroupSeminormClass F α R] {f : F} (nonarch : IsNonarchimedean f) {s : Finset β} {l : β → α}
    {k : β} (hk : k ∈ s) (hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)) :
    f (∑ i ∈ s, l i) = f (l k) := by
  have : s.Nonempty := by use k
  induction this using Nonempty.cons_induction generalizing k with
  | singleton a => simp_all
  | cons a s _ hs _ =>
    by_cases ha : k = a
    · rw [sum_cons, ha]
      apply IsNonarchimedean.add_eq_left_of_lt nonarch
      grw [IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean nonarch hs]
      grind [sup'_lt_iff]
    · grind [IsNonarchimedean.add_eq_right_of_lt nonarch]

