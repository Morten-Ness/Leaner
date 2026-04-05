import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem div_eq_div_of_div_eq_div (hc : c ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) : a / c = b / d := have hb : b ≠ 0 := by
    intro hb
    rw [hb, div_zero] at h
    exact div_ne_zero hc hd h.symm
  (div_eq_div_iff_div_eq_div' hb hc).mp h

