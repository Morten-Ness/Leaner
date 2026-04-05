import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

theorem prod_boole : ∏ i ∈ s, (ite (p i) 1 0 : M₀) = ite (∀ i ∈ s, p i) 1 0 := by
  rw [Finset.prod_ite_zero, prod_const_one]

