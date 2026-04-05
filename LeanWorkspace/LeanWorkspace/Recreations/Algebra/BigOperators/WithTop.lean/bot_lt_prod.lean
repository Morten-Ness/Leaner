import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithBot M₀}

theorem bot_lt_prod [LT M₀] (h : ∀ i ∈ s, ⊥ < f i) : ⊥ < ∏ i ∈ s, f i := prod_induction f (⊥ < ·) (fun _ _ ↦ bot_lt_mul) (bot_lt_coe _) h

