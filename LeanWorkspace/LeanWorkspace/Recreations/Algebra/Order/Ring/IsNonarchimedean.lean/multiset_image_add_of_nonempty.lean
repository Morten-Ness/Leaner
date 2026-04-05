import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

omit [Semiring R] in
theorem multiset_image_add_of_nonempty {α β : Type*} [AddCommMonoid α] [Nonempty β] {f : α → R}
    (hna : IsNonarchimedean f) (g : β → α) {s : Multiset β} (hs : s ≠ 0) :
    ∃ b : β, (b ∈ s) ∧ f (Multiset.map g s).sum ≤ f (g b) := by
  induction s using Multiset.induction_on with
  | empty => contradiction
  | cons a s h =>
    simp only [Multiset.mem_cons, Multiset.map_cons, Multiset.sum_cons, exists_eq_or_imp]
    by_cases h1 : s = 0
    · simp [h1]
    · obtain ⟨w, h2, h3⟩ := h h1
      rcases le_max_iff.mp <| hna (g a) (Multiset.map g s).sum with h4 | h4
      · exact .inl h4
      · exact .inr ⟨w, h2, le_trans h4 h3⟩

