import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

variable [Nontrivial M₀] [NoZeroDivisors M₀]

theorem prod_ne_zero_iff : ∏ x ∈ s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 := by
  rw [Ne, Finset.prod_eq_zero_iff]
  push Not; rfl

