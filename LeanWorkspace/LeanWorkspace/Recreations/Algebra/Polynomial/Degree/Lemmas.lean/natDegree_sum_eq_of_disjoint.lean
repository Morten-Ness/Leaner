import Mathlib

open scoped Function -- required for scoped `on` notation Polynomial

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem natDegree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on natDegree ∘ f)) :
    natDegree (s.sum f) = s.sup fun i => natDegree (f i) := by
  by_cases! H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [Polynomial.degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
        Finset.sup'_eq_sup hs]
      refine le_antisymm ?_ ?_
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases hb' : f b = 0
        · simpa [hb'] using hs
        rw [degree_eq_natDegree hb', Nat.cast_withBot]
        exact Finset.le_sup' (fun i : S => (natDegree (f i) : WithBot ℕ)) hb
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, Function.comp_apply]
        by_cases hb' : f b = 0
        · refine ⟨x, hx, ?_⟩
          contrapose! hx'
          simpa [← Nat.cast_withBot, hb', degree_eq_bot] using hx'
        exact ⟨b, hb, (degree_eq_natDegree hb').ge⟩
    · exact h.imp fun x y hxy hxy' => hxy (natDegree_eq_of_degree_eq hxy')
  · rw [Finset.sum_eq_zero H, natDegree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]

