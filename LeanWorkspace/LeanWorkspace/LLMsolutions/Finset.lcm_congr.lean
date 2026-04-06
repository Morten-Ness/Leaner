FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by
  subst hs
  classical
  induction s₂ using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp only [Finset.lcm_insert, ha]
      rw [hfg a (by simp)]
      apply congrArg (fun x => gcdMonoid.lcm (g a) x)
      apply ih
      intro b hb
      exact hfg b (by simp [hb])
