import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_ex_top (h : ∏ j ∈ s, f j = ⊤) : ∃ i ∈ s, f i = ⊤ := by
  contrapose! h
  exact WithTop.prod_ne_top h

