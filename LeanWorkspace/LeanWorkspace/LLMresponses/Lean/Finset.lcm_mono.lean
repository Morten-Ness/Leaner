FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f := by
  classical
  refine Finset.induction_on s₂ ?_ ?_ s₁ h
  · intro s₁ hs
    have hs₁ : s₁ = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.2
      intro a ha
      exact hs ha
    rw [hs₁]
    simp
  · intro a t hat ih s₁ hs
    by_cases has : a ∈ s₁
    · have herase : s₁.erase a ⊆ t := by
        intro b hb
        have hb' : b ∈ s₁ := Finset.mem_of_mem_erase hb
        have : b ∈ insert a t := hs hb'
        rw [Finset.mem_insert] at this
        rcases this with rfl | hbt
        · exact False.elim (Finset.not_mem_erase _ _ hb)
        · exact hbt
      have hdvd : (s₁.erase a).lcm f ∣ t.lcm f := ih (s₁.erase a) herase
      have hs₁ : s₁ = insert a (s₁.erase a) := (Finset.insert_erase has).symm
      rw [hs₁, Finset.lcm_insert, Finset.lcm_insert]
      exact dvd_lcm (dvd_refl _) hdvd
      · simpa using has
      · simpa using hat
    · have hs' : s₁ ⊆ t := by
        intro b hb
        have : b ∈ insert a t := hs hb
        rw [Finset.mem_insert] at this
        rcases this with rfl | hbt
        · exact False.elim (has hb)
        · exact hbt
      have hdvd : s₁.lcm f ∣ t.lcm f := ih s₁ hs'
      rw [Finset.lcm_insert]
      exact dvd_trans hdvd (dvd_lcm_right _ _)
      · simpa using hat
