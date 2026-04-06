FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f := by
  classical
  refine Finset.induction_on s₁ ?_ ?_
  · simp
  · intro a t ha ih
    have hat : a ∈ s₂ := h (by simp [ha])
    rw [Finset.gcd_insert]
    · refine dvd_gcd ?_ ?_
      · exact Finset.gcd_dvd _ _ _
      · exact ih (by
          intro x hx
          exact h (by simp [hx, ha]))
    · exact ha
