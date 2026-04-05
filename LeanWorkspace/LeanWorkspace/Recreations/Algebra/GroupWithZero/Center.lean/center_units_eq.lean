import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

theorem center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := Set.center_units_subset.antisymm subset_center_units

