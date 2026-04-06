FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    by_cases hmem : g a ∈ s.image g
    · rw [Finset.image_insert]
      rw [Finset.lcm_cons]
      simp [ha, hmem, ih]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_insert_self _ _, rfl⟩
    · rw [Finset.image_insert]
      rw [Finset.lcm_insert]
      · simp [ha, hmem, ih]
      · exact hmem
