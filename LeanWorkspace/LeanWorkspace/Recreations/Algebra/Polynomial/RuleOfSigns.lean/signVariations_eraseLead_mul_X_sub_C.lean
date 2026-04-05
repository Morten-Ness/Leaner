import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

theorem signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.signVariations = ((X - C η) * P.eraseLead).signVariations := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_one.mpr (natDegree_pos_of_nextCoeff_ne_zero hc.ne)
  have hndxP : natDegree ((X - C η) * P) = P.natDegree + 1 := by
    have hPn0 : P ≠ 0 :=
      leadingCoeff_ne_zero.mp hP₀.ne'
    rw [natDegree_mul (X_sub_C_ne_zero η) hPn0, natDegree_X_sub_C, add_comm]
  have hndxeP : natDegree ((X - C η) * P.eraseLead) = P.natDegree := by
    have hePn0 : P.eraseLead ≠ 0 :=
      mt nextCoeff_eq_zero_of_eraseLead_eq_zero hc.ne
    rw [natDegree_mul (X_sub_C_ne_zero η) hePn0, natDegree_X_sub_C, add_comm]
    exact natDegree_eraseLead_add_one hc.ne
  have hQ : ((X - C η) * P).nextCoeff = coeff P d - η * coeff P (d + 1) := by
    grind [nextCoeff_of_natDegree_pos, coeff_X_sub_C_mul]
  have hQ₁ : ((X - C η) * P).nextCoeff < 0 := by
    rw [hQ, sub_neg]
    trans 0
    · grind [nextCoeff_of_natDegree_pos]
    · exact hd ▸ mul_pos hη hP₀
  have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = P.natDegree := by
    apply Nat.add_right_cancel (m := 1)
    rw [← hndxP, natDegree_eraseLead_add_one hQ₁.ne]
  --the theorem is true mainly because all the signs are the same;
  --in fact, the coefficients are all the same except the first.
  suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * P.eraseLead) by
    suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
      (coeffList ((X - C η) * P.eraseLead)).map SignType.sign by
        rw [Polynomial.signVariations, Polynomial.signVariations, this]
    have : 0 < natDegree ((X - C η) * P.eraseLead) := by lia
    grind [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, leadingCoeff_eraseLead_eq_nextCoeff,
      LT.lt.ne, sign_neg, coeffList_eraseLead, ne_zero_of_natDegree_gt,
      nextCoeff_eq_zero_of_eraseLead_eq_zero]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_eraseLead_eq_nextCoeff hQ₁.ne]
  rw [hndexP0, ← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
  rw [hndxeP, hndxP]
  rw [leadingCoeff_eraseLead_eq_nextCoeff hc.ne, ← self_sub_monomial_natDegree_leadingCoeff]
  rw [hQ, mul_sub, sub_mul, sub_mul, X_mul_monomial, C_mul_monomial, monomial_sub]
  rw [leadingCoeff, nextCoeff_of_natDegree_pos (hd ▸ d.succ_pos), hd, Nat.add_sub_cancel]
  abel

