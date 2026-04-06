FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha' : f a ∣ g a := h a (by simp)
      have hs' : ∀ b ∈ s, f b ∣ g b := by
        intro b hb
        exact h b (by simp [hb])
      rw [Finset.lcm_insert, Finset.lcm_insert]
      · exact dvd_lcm ha' (ih hs')
      · exact ha
      · exact ha
