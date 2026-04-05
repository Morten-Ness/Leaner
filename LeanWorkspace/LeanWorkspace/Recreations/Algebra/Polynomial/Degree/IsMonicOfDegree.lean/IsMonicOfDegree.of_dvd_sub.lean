import Mathlib

variable {R : Type*}

variable [CommRing R]

theorem IsMonicOfDegree.of_dvd_sub {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a - r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b + r := by
  convert ha.of_dvd_add hmn hb ?_ h using 4 with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]

