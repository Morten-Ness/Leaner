FAIL
import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

theorem gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  simpa using (Finset.gcd_div_id_eq_one (s := s) (a := i) his hfi)
