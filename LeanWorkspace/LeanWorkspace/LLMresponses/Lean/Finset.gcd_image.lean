FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      by_cases hmem : g a ∈ s.image g
      · rw [Finset.image_insert]
        simp [hmem, ih]
        exact Finset.gcd_eq_right.2 hmem
      · simp [Finset.image_insert, hmem, ih]
