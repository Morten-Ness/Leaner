import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  induction s₁ using Finset.cons_induction_on with
  | empty =>
      simp
  | @cons a s ha ih =>
      rw [Finset.gcd_cons]
      rw [Finset.gcd_cons]
      rw [hfg a (by simp)]
      rw [ih]
      intro b hb
      exact hfg b (by simp [hb])
