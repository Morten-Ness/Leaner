import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) :
    p.spanRank.toENat = ⨅ (s : {s : Finset M // span R s = p}), (s.1.card : ℕ∞) := by
  rw [Submodule.spanRank_toENat_eq_iInf_encard]
  rcases eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤ with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s ↦ False.elim (Set.encard_ne_top_iff.mpr s.1.finite_toSet (h1 s.1 s.2))
  · simp_rw [← Set.encard_coe_eq_coe_finsetCard]
    apply le_antisymm
    · exact le_iInf fun s ↦ iInf₂_le (s.1 : Set M) s.2
    · refine le_iInf fun s ↦ le_iInf fun h ↦ ?_
      by_cases hs : s.Finite
      · exact iInf_le_of_le ⟨hs.toFinset, by simpa⟩ (by simp)
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

