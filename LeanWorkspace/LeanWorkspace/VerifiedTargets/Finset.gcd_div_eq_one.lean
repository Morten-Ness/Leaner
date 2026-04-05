import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

theorem gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha ↦ ?_).trans hg
  rw [he a ha, mul_div_cancel_left₀]
  exact mt Finset.gcd_eq_zero_iff.1 fun h ↦ hfi <| h i his

