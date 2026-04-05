import Mathlib

variable {α β : Type*}

variable [LinearOrderedCommGroupWithZero α] {a b c d : α} {m n : ℕ}

theorem denselyOrdered_iff_denselyOrdered_units_and_nontrivial_units :
    DenselyOrdered α ↔ Nontrivial αˣ ∧ DenselyOrdered αˣ := by
  refine ⟨fun H ↦ ⟨?_, ?_⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  · obtain ⟨x, hx, hx'⟩ := exists_between (zero_lt_one' α)
    exact ⟨Units.mk0 x hx.ne', 1, by simpa [Units.ext_iff] using hx'.ne⟩
  · refine ⟨fun x y h ↦ ?_⟩
    obtain ⟨z, hz⟩ := exists_between (Units.val_lt_val.mpr h)
    refine ⟨Units.mk0 z (ne_zero_of_lt hz.1), by simp [← Units.val_lt_val, hz]⟩
  · refine ⟨fun x y h ↦ ?_⟩
    lift y to αˣ using (ne_zero_of_lt h).isUnit
    obtain rfl | hx := (zero_le' (a := x)).eq_or_lt
    · obtain ⟨z, hz⟩ := exists_one_lt' (α := αˣ)
      exact ⟨(y * z⁻¹ : αˣ), by simp, Units.val_lt_val.mpr <| by simp [hz]⟩
    · lift x to αˣ using hx.ne'.isUnit
      obtain ⟨z, hz, hz'⟩ := H₂.dense x y (Units.val_lt_val.mpr h)
      exact ⟨z, by simp [hz, hz']⟩

-- Counterexample with monoid: `{ x : ℝ | 0 ≤ x ≤ 1 }`

