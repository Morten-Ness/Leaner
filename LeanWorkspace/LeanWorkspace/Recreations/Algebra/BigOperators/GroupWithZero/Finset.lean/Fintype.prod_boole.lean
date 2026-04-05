import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [Fintype ι] [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀}

theorem prod_boole : ∏ i, (ite (p i) 1 0 : M₀) = ite (∀ i, p i) 1 0 := by simp [Finset.prod_boole]

