import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_iff : ∏ j ∈ s, f j = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ (∀ i ∈ s, f i ≠ 0) := by
  constructor
  · exact fun h ↦ ⟨WithTop.prod_eq_top_ex_top h, fun _ ih ↦ WithTop.prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ ↦ WithTop.prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

