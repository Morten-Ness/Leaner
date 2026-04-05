import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [Fintype ι] [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀}

theorem prod_ite_zero : (∏ i, if p i then f i else 0) = if ∀ i, p i then ∏ i, f i else 0 := by
  simp [Finset.prod_ite_zero]

