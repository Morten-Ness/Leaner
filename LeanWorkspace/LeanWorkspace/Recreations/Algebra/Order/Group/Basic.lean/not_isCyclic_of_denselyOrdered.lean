import Mathlib

variable {α : Type*}

variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α] {n : ℤ} {a b : α}

theorem not_isCyclic_of_denselyOrdered [DenselyOrdered α] [Nontrivial α] : ¬IsCyclic α := by
  intro h
  rcases exists_zpow_surjective α with ⟨a, ha⟩
  rcases lt_trichotomy a 1 with hlt | rfl | hlt
  · rcases exists_between hlt with ⟨b, hab, hb⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    rw [← one_lt_inv'] at hlt
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all
  · rcases exists_ne (1 : α) with ⟨b, hb⟩
    simpa [hb.symm] using ha b
  · rcases exists_between hlt with ⟨b, hb, hba⟩
    rcases ha b with ⟨k, rfl⟩
    suffices 0 < k ∧ k < 1 by lia
    simp_rw [← zpow_lt_zpow_iff_right hlt]
    simp_all

