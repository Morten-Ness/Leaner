import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

set_option backward.isDefEq.respectTransparency false in
theorem irreducible_aux1 {k m n : ℕ} (hkm : k < m) (hmn : m < n) (u v w : Units ℤ)
    (hp : p = Polynomial.trinomial k m n (u : ℤ) v w) :
    C (v : ℤ) * (C (u : ℤ) * X ^ (m + n) + C (w : ℤ) * X ^ (n - m + k + n)) =
      ⟨Finsupp.filter (· ∈ Set.Ioo (k + n) (n + n)) (p * p.mirror).toFinsupp⟩ := by
  have key : n - m + k < n := by rwa [← lt_tsub_iff_right, tsub_lt_tsub_iff_left_of_le hmn.le]
  rw [hp, Polynomial.trinomial_mirror hkm hmn Polynomial.IsUnitTrinomial.ne_zero u Polynomial.IsUnitTrinomial.ne_zero w]
  simp_rw [Polynomial.trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial,
    toFinsupp_add, toFinsupp_monomial, AddMonoidAlgebra, Finsupp.filter_add]
  rw [Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos,
    Finsupp.filter_single_of_neg, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]
  · simp only [add_zero, zero_add]
    -- Porting note: the next `rw` is needed to see through the defeq `Finsupp = AddMonoidAlgebra`
    rw [ofFinsupp_add]
    simp only [ofFinsupp_single]
    rw [C_mul_monomial, C_mul_monomial, mul_comm (v : ℤ) w, add_comm (n - m + k) n]
  · exact fun h => h.2.ne rfl
  · refine ⟨?_, by gcongr⟩
    rwa [add_comm, add_lt_add_iff_left, lt_add_iff_pos_left, tsub_pos_iff_lt]
  · exact fun h => h.1.ne (add_comm k n)
  · constructor <;> gcongr
  · rw [← add_assoc, add_tsub_cancel_of_le hmn.le, add_comm]
    exact fun h => h.1.ne rfl
  · grind
  · exact fun h => h.1.ne rfl
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) key
  · exact fun h => asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn)

