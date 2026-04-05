import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem IsMonicOfDegree.of_dvd_add {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a + r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b - r := by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq, show m - n + n = m by lia]
  exact ha.add_right hr

