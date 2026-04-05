import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithBot M₀}

theorem prod_ne_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ∏ i ∈ s, f i ≠ ⊥ := prod_induction f (· ≠ ⊥) (fun _ _ ↦ mul_ne_bot) coe_ne_bot h

