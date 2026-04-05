import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_ne_zero (hi : i ∈ s) (h : ∏ j ∈ s, f j = ⊤) : f i ≠ 0 := by
  by_contra! h0
  apply WithTop.top_ne_zero (α := M₀)
  calc
    ⊤ = ∏ j ∈ s, f j := Eq.symm h
    _ = 0 := prod_eq_zero hi h0

