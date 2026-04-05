import Mathlib

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

theorem center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := Set.center_units_subset.antisymm subset_center_units

end

section

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

theorem center_units_subset : center G₀ˣ ⊆ ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
  · exact congr_arg Units.val <| hu <| Units.mk0 a ha

end
