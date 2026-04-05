import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_card
    exact support_monomial' _ _

