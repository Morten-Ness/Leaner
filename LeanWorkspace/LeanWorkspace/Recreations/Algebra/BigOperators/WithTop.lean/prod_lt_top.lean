import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_lt_top [LT M₀] (h : ∀ i ∈ s, f i < ⊤) : ∏ i ∈ s, f i < ⊤ := prod_induction f (· < ⊤) (fun _ _ ↦ mul_lt_top) (coe_lt_top _) h

