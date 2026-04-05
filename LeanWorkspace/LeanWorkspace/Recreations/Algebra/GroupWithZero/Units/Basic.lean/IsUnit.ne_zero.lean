import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 := let ⟨u, hu⟩ := ha
  hu ▸ Units.ne_zero u

