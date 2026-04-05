import Mathlib

theorem uniqueMul_of_twoUniqueMul {G} [Mul G] {A B : Finset G} (h : 1 < #A * #B →
    ∃ p1 ∈ A ×ˢ B, ∃ p2 ∈ A ×ˢ B, p1 ≠ p2 ∧ UniqueMul A B p1.1 p1.2 ∧ UniqueMul A B p2.1 p2.2)
    (hA : A.Nonempty) (hB : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, UniqueMul A B a b := by
  by_cases! +distrib hc : #A ≤ 1 ∧ #B ≤ 1
  · exact UniqueMul.of_card_le_one hA hB hc.1 hc.2
  rw [← Finset.card_pos] at hA hB
  obtain ⟨p, hp, _, _, _, hu, _⟩ := h (Nat.one_lt_mul_iff.mpr ⟨hA, hB, hc⟩)
  rw [Finset.mem_product] at hp
  exact ⟨p.1, hp.1, p.2, hp.2, hu⟩

