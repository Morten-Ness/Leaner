import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_mul_eq_mul_eraseLead_of_nextCoeff_zero {R : Type*} [Ring R] [NoZeroDivisors R]
    [Nontrivial R] {x : R} {P : R[X]} (hx : x ≠ 0) (h : P.nextCoeff = 0) :
    ((Polynomial.X - Polynomial.C x) * P).eraseLead.eraseLead = (Polynomial.X - Polynomial.C x) * P.eraseLead := by
  -- if `P = 0` this is trivial
  by_cases hp : P = 0
  · simp [hp]
  -- can assume Polynomial.eraseLead P ≠ 0, otherwise it's a monomial and both sides are zero.
  by_cases he : P.eraseLead = 0
  · rw [he, mul_zero]
    by_cases he₂ : ((Polynomial.X - Polynomial.C x) * P).eraseLead = 0
    · simp [he₂]
    suffices #((Polynomial.X - Polynomial.C x) * P).support ≤ 2 by
      rw [← card_support_eq_zero]
      linarith [Polynomial.eraseLead_support_card_lt he₂,
        Polynomial.eraseLead_support_card_lt (mul_ne_zero (X_sub_C_ne_zero x) hp)]
    have h₂ : #(Polynomial.X - Polynomial.C x).support = 2 := by
      simpa [← sub_eq_add_neg] using
        card_support_binomial one_ne_zero one_ne_zero (neg_ne_zero.mpr hx)
    have hmul := card_support_mul_le (p := Polynomial.X - Polynomial.C x) (q := P)
    rw [h₂] at hmul
    linarith [Polynomial.card_support_le_one_of_eraseLead_eq_zero he]
  have h₁ : ((Polynomial.X - Polynomial.C x) * P).natDegree = P.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero x) hp, Polynomial.natDegree_X_sub_C, add_comm]
  -- 2 ≤ P.natDegree
  obtain ⟨dP, hdP⟩ := Nat.exists_eq_add_of_le' (Polynomial.two_le_natDegree_of_nextCoeff_eraseLead he h)
  -- the subleading term of (Polynomial.X - Polynomial.C η) * P is nonzero
  have h₂ : ((Polynomial.X - Polynomial.C x) * P).nextCoeff ≠ 0 := by
    simp only [nextCoeff, hdP, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] at h
    rw [nextCoeff, h₁, add_tsub_cancel_right, hdP, coeff_X_sub_C_mul]
    simp [h, hx, ← hdP, hp]
  -- Prove equality by showing coefficients are equal
  ext n
  rcases n.lt_or_ge P.natDegree with hn | hn
  · --n < P.natDegree
    have hd₁ : n < ((Polynomial.X - Polynomial.C x) * P).eraseLead.natDegree := by
      linarith [Polynomial.natDegree_eraseLead_add_one h₂]
    rw [← Polynomial.self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial, if_neg hd₁.ne']
    rw [← Polynomial.self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial, if_neg (by lia)]
    rw [← Polynomial.self_sub_monomial_natDegree_leadingCoeff, mul_sub, coeff_sub,
      sub_zero, sub_zero, eq_sub_iff_add_eq, add_eq_left]
    rcases hn₂ : n
    · simpa [coeff_monomial, hp] using fun _ ↦ by lia
    · rw [coeff_X_sub_C_mul, coeff_monomial, coeff_monomial, if_neg (by lia),
        if_neg (by lia), mul_zero, sub_zero]
  · --n ≥ P.natDegree, so all the coefficients are zero.
    trans 0 <;> rw [coeff_eq_zero_of_natDegree_lt]
    · grw [Polynomial.eraseLead_natDegree_le, Polynomial.eraseLead_natDegree_le]
      simpa [h₁, hdP] using hn
    · grw [natDegree_mul (X_sub_C_ne_zero x) he, Polynomial.natDegree_eraseLead_le_of_nextCoeff_eq_zero h]
      simpa [add_comm, hdP] using hn

