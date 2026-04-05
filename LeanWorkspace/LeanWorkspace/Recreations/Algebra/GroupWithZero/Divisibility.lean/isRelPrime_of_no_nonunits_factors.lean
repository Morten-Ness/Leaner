import Mathlib

variable {α : Type*}

theorem isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z, ¬ IsUnit z → z ≠ 0 → z ∣ x → ¬z ∣ y) : IsRelPrime x y := by
  refine fun z hx hy ↦ by_contra fun h ↦ H z h ?_ hx hy
  rintro rfl; exact nonzero ⟨zero_dvd_iff.1 hx, zero_dvd_iff.1 hy⟩

