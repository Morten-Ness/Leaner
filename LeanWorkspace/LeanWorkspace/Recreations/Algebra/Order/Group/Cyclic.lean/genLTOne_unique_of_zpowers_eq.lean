import Mathlib

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]

variable (H : Subgroup G) [Nontrivial H] [hH : IsCyclic H]

theorem genLTOne_unique_of_zpowers_eq {g1 g2 : G} (hg1 : g1 < 1) (hg2 : g2 < 1)
    (h : LinearOrderedCommGroup.Subgroup.zpowers g1 = LinearOrderedCommGroup.Subgroup.zpowers g2) : g1 = g2 := by
  rcases (LinearOrderedCommGroup.Subgroup.zpowers g2).bot_or_nontrivial with (h' | h')
  · rw [h'] at h
    simp_all only [LinearOrderedCommGroup.Subgroup.zpowers_eq_bot]
  · have h1 : IsCyclic ↥(LinearOrderedCommGroup.Subgroup.zpowers g2) := by
      rw [LinearOrderedCommGroup.Subgroup.isCyclic_iff_exists_zpowers_eq_top]; use g2
    have h2 : Nontrivial ↥(LinearOrderedCommGroup.Subgroup.zpowers g1) := by rw [h]; exact h'
    have h3 : IsCyclic ↥(LinearOrderedCommGroup.Subgroup.zpowers g1) := by rw [h]; exact h1
    simp only [LinearOrderedCommGroup.Subgroup.genLTOne_unique (LinearOrderedCommGroup.Subgroup.zpowers g2) hg1 h]
    simp only [← h]
    simp only [LinearOrderedCommGroup.Subgroup.genLTOne_unique (LinearOrderedCommGroup.Subgroup.zpowers g1) hg2 h.symm]

