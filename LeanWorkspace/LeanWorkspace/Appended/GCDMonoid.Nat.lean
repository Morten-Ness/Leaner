import Mathlib

section

theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  cases le_total 0 z <;>
  simp [abs_of_nonneg, abs_of_nonpos, Int.normalize_of_nonneg, Int.normalize_of_nonpos, *]

end

section

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b := dvd_antisymm_of_normalize_eq (Int.normalize_of_nonneg ha) (Int.normalize_of_nonneg hb) h.dvd h.symm.dvd

end

section

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z := ⟨Int.nonneg_of_normalize_eq_self, Int.normalize_of_nonneg⟩

end

section

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z := by
  by_cases! h : 0 ≤ z
  · exact h
  · rw [Int.normalize_of_nonpos h.le] at hz
    lia

end

section

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  rw [normalize_apply, Int.normUnit_eq, if_pos h, Units.val_one, mul_one]

end

section

theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  obtain rfl | h := h.eq_or_lt
  · simp
  · rw [normalize_apply, Int.normUnit_eq, if_neg (not_le_of_gt h), Units.val_neg, Units.val_one,
      mul_neg_one]

end
