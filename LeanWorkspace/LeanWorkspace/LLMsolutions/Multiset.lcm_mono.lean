FAIL
import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm := by
  refine Multiset.induction_on s₁ ?base ?step
  · simp
  · intro a s ih
    have ha : a ∈ s₂ := h (by simp)
    rcases Multiset.exists_cons_of_mem ha with ⟨t, rfl⟩
    have hs : s ⊆ t := by
      intro b hb
      have hb' : b ∈ a ::ₘ t := h (by simp [hb])
      simp only [Multiset.mem_cons] at hb'
      cases hb' with
      | inl hba =>
          subst hba
          exact Multiset.mem_of_subset (show s ⊆ a ::ₘ t from by
            intro c hc
            exact h (by simp [hc])) (by simp)
      | inr hbt =>
          exact hbt
    have hst : s.lcm ∣ t.lcm := ih hs
    rw [Multiset.lcm_cons, Multiset.lcm_cons]
    exact lcm_dvd ha (dvd_trans (dvd_lcm_right a s.lcm) (by simpa [Multiset.lcm_cons] using hst))
